-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_6_2
-- name    : GeoRobustLearn.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:33.818665+00:00
-- url     : https://prove2.me/theorems/24577d38-dfe8-4c12-aa13-98395a3e9b51
-- title:
--   Lemma 6.2 — Algorithm 3 finds a three-threshold mixture with error and danger within $\varepsilon$ of their averages
-- statement:
--   There are a program $A$ of the arithmetic real RAM with an evaluation oracle and a constant $C$ such that the following holds. Let $d\ge1$, let $P:\mathbb R^{d+1}\to\mathbb R$ be measurable with evaluation cost $T\ge d+1$, $r\in\mathbb R$, $\varepsilon,\delta\in(0,1)$, and let $D$ be a distribution on $\mathbb R^d\times\{0,1\}$ with first marginal $\gamma$. Then on every sample stream $A$ halts within $C\varepsilon^{-3}\log\frac2{\varepsilon\delta}\,T$ steps and outputs thresholds $\vec\theta\in(0,1)^3$ and weights $\vec w\in\Delta_3$; and with probability at least $1-\delta$,
--
--   $$\sum_{i=1}^3w_i\Pr_{(x,y)\sim D}[g_{\theta_i}(x)\ne y]\le\mathbb E|\bar p(x)-y|+\varepsilon,\qquad \sum_{i=1}^3w_i\Pr_{x\sim\gamma}[\theta_i\in I_r(x)]\le\mathbb E|I_r(x)|+\varepsilon.$$
--
--   A random threshold has expected error $\mathbb E|\bar p-y|$ and expected danger $\mathbb E|I_r|$; this lemma replaces it by a mixture of only three thresholds, which the partition step can derandomize.
--
--   Differences from the source:
--   - reading: "the algorithm runs in time … T_eval(P)" → ∃ one program of the arithmetic real RAM with an evaluation oracle (OracleMachine), chosen before all data; evalP costs T; reason: T_eval(P) is the time to evaluate P at one point; arithmetic-only as for the goal (paper.md decisions 4, 11)
--   - reading: T_eval(P) ≥ 1 → T ≥ d + 1; reason: evaluating P reads a point of ℝ^{d+1}, and one sample costs d + 1 in this machine (paper.md decision 11)
--   - generalization: P a smoothed polynomial → any measurable P : Space (d+1) → ℝ; reason: the algorithm and its analysis use only evaluations of P; a smoothed polynomial is measurable
--   - generalization: r a radius → any real r; reason: the algorithm and its analysis do not use the sign of r
--   - reading: d (dimension, unconstrained in the statement) → 1 ≤ d; reason: standing assumption of §5.1 (p.22); Theorem 6.1 is false at d = 0 (paper.md decision 6)
--   - encoding: D a distribution on ℝ^d × {0, 1} whose first marginal is γ → a probability measure on Space d × ℝ with GaussianInput D and labels in {0, 1} D-a.s. (BinaryLabels); reason: Lean representation; same instances
--   - encoding: O(ε⁻³ log(1/(εδ)) T_eval(P)) → C·ε⁻³·log(2/(εδ))·T with C before all data; reason: the meaning of O(·); log(2/·) stays bounded below as ε, δ → 1 where log(1/(εδ)) → 0
--   - reading: the Ensure line θ⃗ ∈ (0,1)³, w⃗ ∈ Δ₃ and the time bound → conclusions on every stream; output block [θ₁, θ₂, θ₃, w₁, w₂, w₃]; reason: Algorithm 3's loops are bounded and its output format is fixed; the goal uses both
--   - reading: "with probability at least 1 − δ" → a measurable event of mass ≥ 1 − δ under the stream law (HighProbability); reason: the published success-event convention; a stronger conclusion
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 6.2 and Algorithm 3, pp.31–33 (PDF pp.31–33)

import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_DangerInterval
import Definitions.Def_GeoRobustLearn_OracleMachine

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 6.2** (three-threshold mixture, Algorithm 3 ComputeRoundingThresholds), pp.31–33.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There are one program `A` of the oracle machine and a constant `C` such that for every `d ≥ 1`, every
measurable `P : ℝ^{d+1} → ℝ` evaluated at cost `T ≥ d + 1`, every `r`, `ε, δ ∈ (0, 1)` and every
distribution `D` on `ℝ^d × {0, 1}` with first marginal `γ`: on every stream `A` halts within
`C ε⁻³ log(2/(εδ)) T` steps and outputs `θ⃗ ∈ (0, 1)³` and `w⃗ ∈ Δ₃` (the block
`[θ₁, θ₂, θ₃, w₁, w₂, w₃]`); and on a measurable event of probability at least `1 − δ`,
`Σᵢ wᵢ Pr_D[g_{θᵢ}(x) ≠ y] ≤ E|p̄(x) − y| + ε` and `Σᵢ wᵢ Pr_{x∼γ}[θᵢ ∈ I_r(x)] ≤ E|I_r(x)| + ε`.

**Formalization Note.** `T_eval(P)` is the cost `T` of the oracle instruction `evalP`
(`OracleMachine`), and `T ≥ d + 1` since an evaluation reads a point of `ℝ^{d+1}` (a sample costs
`d + 1` in this machine). `O(ε⁻³ log(1/(εδ)) T)` is `C ε⁻³ log(2/(εδ)) T` with `C` chosen before all
data (`log(2/·)` keeps the bound positive as `ε, δ → 1`). `P` is any measurable function (the paper's
`P` is a smoothed polynomial). The inputs `[r, ε, δ]` are the first three memory cells. Probabilities
are (outer) measures in `[0, ∞]`; `|I_r(x)|` is the Lebesgue measure of the danger interval. -/
theorem lemma_6_2 :
    ∃ (A : OProgram) (C : ℕ), OAdmissible A ∧ 0 < C ∧
      ∀ (d T : ℕ) (P : Space (d+1) → ℝ) (r ε δ : ℝ) (D : Measure (Space d × ℝ)),
        1 ≤ d → Measurable P → d + 1 ≤ T →
        IsProbabilityMeasure D → GaussianInput D → BinaryLabels D →
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let R : ℝ := C * ε⁻¹ ^ 3 * Real.log (2 / (ε * δ)) * T
        let S : Streams d → State := fun ω => orun d P T A ω (initial d 0 [r, ε, δ]) ⌈R⌉₊
        let θ : Streams d → Fin 3 → ℝ := fun ω i => (representation (S ω))[i.val]!
        let w : Streams d → Fin 3 → ℝ := fun ω i => (representation (S ω))[3 + i.val]!
        (∀ ω, (S ω).halted = true ∧ ((S ω).work : ℝ) ≤ R ∧
          (representation (S ω)).length = 6 ∧
          (∀ i, 0 < θ ω i ∧ θ ω i < 1) ∧ (∀ i, 0 ≤ w ω i) ∧ ∑ i, w ω i = 1) ∧
        HighProbability (streamLaw D) δ (fun ω =>
          ∑ i, ENNReal.ofReal (w ω i) * D {z | clipThreshold P (θ ω i) z.1 ≠ z.2} ≤
            ∫⁻ z, ENNReal.ofReal |pbar P z.1 - z.2| ∂D + ENNReal.ofReal ε ∧
          ∑ i, ENNReal.ofReal (w ω i) * gaussian d {x | θ ω i ∈ dangerInterval P r x} ≤
            ∫⁻ x, volume (dangerInterval P r x) ∂gaussian d + ENNReal.ofReal ε) := by sorry

end GeoRobustLearn
