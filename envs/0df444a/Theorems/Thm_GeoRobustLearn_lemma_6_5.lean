-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_6_5
-- name    : GeoRobustLearn.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:36.287917+00:00
-- url     : https://prove2.me/theorems/93ff0d70-2407-46b9-8ae1-a30eb2b4cbfd
-- title:
--   Lemma 6.5 — Algorithm 4 returns a strip partition with at most 24 seams reproducing the mixture within $\varepsilon/3$
-- statement:
--   There are a program $A$ of the arithmetic real RAM with an evaluation oracle and a constant $C$ such that the following holds. Let $d\ge1$, $P:\mathbb R^{d+1}\to\mathbb R$ measurable with evaluation cost $T\ge d+1$, $\vec w\in\Delta_3$, $\vec\theta\in(0,1)^3$, $r\in\mathbb R$, $\varepsilon,\delta\in(0,1)$, and $D$ a distribution on $\mathbb R^d\times\{0,1\}$ with first marginal $\gamma$. Write $\bar N=\varepsilon^{-2}\log\frac2{\varepsilon\delta}$. Then on every sample stream $A$ halts within $C(\bar NT+\bar N^{25})$ steps and outputs a partition $(A_1,A_2,A_3)$ of $\mathbb R^d$ into parallel strips with at most $24$ seams; and with probability at least $1-\delta$, simultaneously for every $j\in[6]$ and $i\in[3]$,
--
--   $$\big|\Pr[(x,y)\in F_j,\ x\in A_i]-w_i\Pr[(x,y)\in F_j]\big|\le\frac\varepsilon3,$$
--
--   and in particular
--
--   $$\sum_{i=1}^3\Pr[(x,y)\in E_i,\ x\in A_i]\le\sum_{i=1}^3w_i\Pr[(x,y)\in E_i]+\varepsilon,$$
--
--   and the same inequality holds with $C_i$ in place of $E_i$.
--
--   This derandomizes the threshold mixture of Lemma 6.2 at the cost of $O(r)$ boundary volume from the seams.
--
--   Differences from the source:
--   - reading: "the algorithm runs in time … T_eval(P)" → ∃ one program of the arithmetic real RAM with an evaluation oracle (OracleMachine), chosen before all data; evalP costs T; reason: T_eval(P) is the time to evaluate P at one point; arithmetic-only as for the goal (paper.md decisions 4, 11)
--   - reading: T_eval(P) ≥ 1 → T ≥ d + 1; reason: evaluating P reads a point of ℝ^{d+1}, and one sample costs d + 1 in this machine (paper.md decision 11)
--   - generalization: P a smoothed polynomial → any measurable P : Space (d+1) → ℝ; reason: the algorithm and its analysis use only evaluations of P; a smoothed polynomial is measurable
--   - generalization: r a radius → any real r; reason: the algorithm and its analysis do not use the sign of r
--   - reading: d (dimension, unconstrained in the statement) → 1 ≤ d; reason: standing assumption of §5.1 (p.22); Theorem 6.1 is false at d = 0 (paper.md decision 6)
--   - encoding: D a distribution on ℝ^d × {0, 1} whose first marginal is γ → a probability measure on Space d × ℝ with GaussianInput D and labels in {0, 1} D-a.s. (BinaryLabels); reason: Lean representation; same instances
--   - encoding: O(N T_eval(P) + N²⁵), N = O(ε⁻² log(1/(εδ))) → C(N̄T + N̄²⁵), N̄ = ε⁻² log(2/(εδ)), C before all data; reason: the meaning of O(·); log(2/·) stays bounded below as ε, δ → 1
--   - reading: the output (A₁, A₂, A₃) represented by seams and colours (S = 24) → on every stream the output block [d₁, …, d_t, ℓ₀, …, ℓ_t] is valid with t ≤ 24 (ValidStrips 24) and A_i = stripPart; reason: Algorithm 4, lines 3 and 14–17; the goal's boundary bound uses the 24 seams
--   - encoding: |Pr[·] − w_i Pr[·]| → absolute difference of the real values (toReal) of the D-measures; reason: D is a probability measure, so the values are finite
--   - reading: "with probability at least 1 − δ" → a measurable event of mass ≥ 1 − δ under the stream law (HighProbability); reason: the published success-event convention; a stronger conclusion
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 6.5 and Algorithm 4, pp.35–37 (PDF pp.35–37)

import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_DangerInterval
import Definitions.Def_GeoRobustLearn_OracleMachine
import Definitions.Def_GeoRobustLearn_StripPartition

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 6.5** (empirical strip partition, Algorithm 4 ComputePartition), pp.35–37.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There are one program `A` of the oracle machine and a constant `C` such that for every `d ≥ 1`, every
measurable `P` evaluated at cost `T ≥ d + 1`, every `w⃗ ∈ Δ₃`, `θ⃗ ∈ (0, 1)³`, `r`, `ε, δ ∈ (0, 1)` and
every distribution `D` on `ℝ^d × {0, 1}` with first marginal `γ`, writing `N̄ = ε⁻² log(2/(εδ))`:
on every stream `A` halts within `C(N̄ T + N̄²⁵)` steps and outputs a strip partition `(A₁, A₂, A₃)`
of `ℝ^d` with at most `24` seams `d₁ ≤ ⋯ ≤ d_t` and colours in `{1, 2, 3}`; and on a measurable event
of probability at least `1 − δ`, simultaneously for every `j ∈ [6]` and `i ∈ [3]`,
`|Pr[(x, y) ∈ F_j, x ∈ A_i] − w_i Pr[(x, y) ∈ F_j]| ≤ ε/3`, and in particular
`Σᵢ Pr[(x, y) ∈ E_i, x ∈ A_i] ≤ Σᵢ w_i Pr[(x, y) ∈ E_i] + ε`, and the same with `C_i` for `E_i`.

**Formalization Note.** The machine is `OracleMachine` with `T_eval(P) = T ≥ d + 1`. The output
block is `[d₁, …, d_t, ℓ₀, …, ℓ_t]` (`StripPartition`, Algorithm 4 line 17), and the bound `t ≤ 24`
(`S = 24`, line 3) is a conclusion on every stream. `O(N T_eval + N²⁵)` with `N = O(ε⁻² log(1/(εδ)))`
is `C(N̄T + N̄²⁵)` with `C` before all data. `(F₁, …, F₆) = (E₁, E₂, E₃, C₁, C₂, C₃)` is `sixEvents`
with `g_i(x) = 1{P(x, 0) ≥ θ_i}`. The inputs `[w₁, w₂, w₃, θ₁, θ₂, θ₃, r, ε, δ]` are the first nine
memory cells. Probabilities are `D`-measures of the events; the absolute differences are taken in `ℝ`. -/
theorem lemma_6_5 :
    ∃ (A : OProgram) (C : ℕ), OAdmissible A ∧ 0 < C ∧
      ∀ (d T : ℕ) (P : Space (d+1) → ℝ) (w θ : Fin 3 → ℝ) (r ε δ : ℝ)
        (D : Measure (Space d × ℝ)),
        1 ≤ d → Measurable P → d + 1 ≤ T →
        IsProbabilityMeasure D → GaussianInput D → BinaryLabels D →
        (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → (∀ i, 0 < θ i ∧ θ i < 1) →
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let Nbar : ℝ := ε⁻¹ ^ 2 * Real.log (2 / (ε * δ))
        let R : ℝ := C * (Nbar * T + Nbar ^ 25)
        let S : Streams d → State := fun ω =>
          orun d P T A ω (initial d 0 [w 0, w 1, w 2, θ 0, θ 1, θ 2, r, ε, δ]) ⌈R⌉₊
        let Apart : Streams d → Fin 3 → Set (Space d) := fun ω i =>
          stripPart (representation (S ω)) i
        (∀ ω, (S ω).halted = true ∧ ((S ω).work : ℝ) ≤ R ∧
          ValidStrips 24 (representation (S ω))) ∧
        HighProbability (streamLaw D) δ (fun ω =>
          (∀ (j : Fin 6) (i : Fin 3),
            |(D (sixEvents P r θ j ∩ {z | z.1 ∈ Apart ω i})).toReal -
              w i * (D (sixEvents P r θ j)).toReal| ≤ ε / 3) ∧
          ∑ i, D (errEvent P (θ i) ∩ {z | z.1 ∈ Apart ω i}) ≤
            ∑ i, ENNReal.ofReal (w i) * D (errEvent P (θ i)) + ENNReal.ofReal ε ∧
          ∑ i, D (dangerEvent P r (θ i) ∩ {z | z.1 ∈ Apart ω i}) ≤
            ∑ i, ENNReal.ofReal (w i) * D (dangerEvent P r (θ i)) + ENNReal.ofReal ε) := by sorry

end GeoRobustLearn
