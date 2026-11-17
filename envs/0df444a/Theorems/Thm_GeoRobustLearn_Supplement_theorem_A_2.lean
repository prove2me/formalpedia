-- Prove2me | Theorems.Thm_GeoRobustLearn_Supplement_theorem_A_2
-- name    : GeoRobustLearn.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:39:12.320189+00:00
-- url     : https://prove2.me/theorems/9e063682-0407-4478-b6e7-726ffa1516a0
-- title:
--   Theorem A.2 — under (22), learning $\mathcal C_{K,\mu}$ for isotropic strongly log-concave $\mu$: error $\mathrm{opt}_{K,\mu}+\varepsilon$, $\mathrm{Bdry}_{r,\mu}(h)\le O(Kr)$
-- statement:
--   Assume the polynomial approximation assumption (22): for every dimension $n$, every $\kappa$-strongly log-concave probability measure $\nu$ on $\mathbb R^n$ ($\kappa>0$), every bounded measurable $F$, every $t>0$ and every integer $k\ge0$,
--
--   $$\inf_{\deg p\le k}\|p-H_tF\|_{L_2(\nu)}^2\le\|F\|_\infty^2(1+\kappa t)^{-(k+1)},\qquad H_tF(z)=\mathbb E_{g\sim\gamma_n}F(z+\sqrt t\,g).$$
--
--   Then there are a training program, which uses exact real arithmetic, random examples and independent standard Gaussian draws, and a deterministic arithmetic-only evaluation program, such that for every $\alpha\in(0,1]$ there is a constant $C=C(\alpha)$ with the following property. Let $d\ge1$, $K\ge1$, $0<r\le1/K$, $\varepsilon,\delta\in(0,1/4)$, let $\mu$ be an isotropic $\alpha$-strongly log-concave probability measure on $\mathbb R^d$ (mean $0$, covariance $I_d$, density $e^{-V}$ with $V(x)-\alpha\|x\|_2^2/2$ convex), and let $D$ be a distribution on $\mathbb R^d\times\{0,1\}$ with first marginal $\mu$. Write $\mathrm{Bdry}_{r,\mu}(f)=\Pr_{x\sim\mu}[\exists z:\|z\|_2\le r,\ f(x)\ne f(x+z)]$, $\mathcal C_{K,\mu}$ for the Boolean $f$ with $\mathrm{Bdry}_{u,\mu}(f)\le Ku$ for all $u>0$, and
--
--   $$\mathrm{opt}_{K,\mu}=\inf_{f\in\mathcal C_{K,\mu}}\Pr_{(x,y)\sim D}[f(x)\ne y],\qquad R=(d+1)^{C(K^2/\varepsilon^2+K^4r^2/\varepsilon^4)(\log(2+K/\varepsilon+1/(Kr)))^C}(\log(2/\delta))^C.$$
--
--   Run on input $(\alpha,K,r,\varepsilon,\delta)$:
--
--   1. on every stream of examples and Gaussians, training halts within $R$ operations, uses at most $R$ samples and returns a representation of at most $R$ reals, and the evaluation program computes the returned hypothesis $h$ at every point within $R$ operations;
--   2. $h$ takes values in $\{0,1\}$;
--   3. with probability at least $1-\delta$,
--   $$\Pr_{(x,y)\sim D}[h(x)\ne y]\le\mathrm{opt}_{K,\mu}+\varepsilon\qquad\text{and}\qquad\mathrm{Bdry}_{r,\mu}(h)\le CKr.$$
--
--   This extends the paper's Gaussian main theorem to isotropic strongly log-concave marginals, conditionally on (22) (Remark A.1: an announced, unverified approximation result); the learner needs no density, score or conditional-sampling oracle.
--
--   **Formalization Note** Assumption (22) is the hypothesis `PolyApprox22`, a closed proposition, not an axiom. Probabilities of possibly non-measurable sets are outer measures, and the constant $C$ is chosen after $\alpha$ but before all other data.
--
--   Differences from the source:
--   - reading: "the modification of Algorithm 2 described below returns … a Boolean hypothesis h"; α "a known constant" → ∃ a training program P and a deterministic evaluation program E, chosen before α and all data; P gets [α, K, r, ε, δ] as input; h is E run on P's output, within the same budget on every query (FormulaBudget); reason: the reading of the published Theorem 6.1 (existence of the learner, bounded evaluator); α is known to the learner, so it is an input rather than built into the program
--   - reading: "sample and real-arithmetic complexity"; the ν_j "can be sampled using examples from D and independent Gaussian variables" (p.44); "requires no density, score, or conditional-sampling oracle" → the published real RAM; P uses only ArithmeticOnly instructions plus standard-Gaussian draws (ArithmeticGauss), E is Deterministic and ArithmeticOnly; no √, exp, log, Φ⁻¹, no oracle; bounds on every stream; reason: the page's learner draws independent Gaussians; nothing else is given to it
--   - encoding: O(Kr), (d + 1)^{Õ_α(K²/ε²+K⁴r²/ε⁴)} poly(log 1/δ); constants may depend on α, the suppressed logs on K, 1/ε, 1/(Kr), not on d → for each α ∈ (0, 1] one natural C = C(α) > 0 chosen before d, K, r, ε, δ, μ, D: Bdry_{r,μ}(h) ≤ CKr and budget robustBound C d K r ε δ; reason: the meaning of O/Õ_α as printed, in the published budget shape of Theorem 6.1
--   - reading: μ has density e^{−V} with V(x) − α‖x‖²/2 convex → LCAntiConc.IsStronglyLogConcave α μ (V : ℝ^d → ℝ ∪ {+∞}, the density may vanish off a convex set); reason: the standard notion of strong log-concavity; the extended-valued reading admits more marginals μ, so it is the stronger theorem and contains the real-valued reading
--   - generalization: (22) for every κ-strongly log-concave probability measure ν on ℝ^n → (22) for every probability measure ν with density e^{−U}, U real-valued on all of ℝ^n and U − (κ/2)‖·‖² convex (PolySampIso.IsStronglyLogConcaveOn ν Set.univ κ); reason: the hypothesis is required only for full-support ν, a subclass, so it is implied by (22) read with extended-valued potentials (and equal to it read with real-valued ones); the theorem therefore specializes to the source's claim; the proof applies (22) only to ν₂ = (μ ∗ N(0, 2tI_d)) ⊗ N(0, b + 2t) (p.46), which has an everywhere positive density
--   - encoding: κ-strongly log-concave → 0 < κ; reason: 'strongly' means positive curvature; for κ ≤ 0 the right-hand side (1 + κt)^{−(k+1)} is not the page's quantity
--   - reading: ‖F‖²_∞ for bounded measurable F → M² for every M with |F(z)| ≤ M for all z (F Borel measurable); reason: the sup norm of a bounded function; every bound M ≥ sup|F| gives a weaker inequality, so this is equivalent to M = sup|F|
--   - encoding: inf_{deg p ≤ k} ‖p − H_tF‖²_{L₂(ν)} → ⨅ over MvPolynomial (Fin n) ℝ of totalDegree ≤ k of ∫⁻ ofReal((p − H_tF)²) dν in ℝ≥0∞, H_tF(z) = ∫ F(z + √t g) dγ_n(g); reason: Lean representation; no junk values (H_tF is a genuine integral for bounded measurable F)
--   - encoding: μ isotropic: mean zero, covariance I_d → IsProbabilityMeasure μ, ∫ x dμ = 0, ∫ ⟨x,u⟩⟨x,v⟩ dμ = ⟨u,v⟩ for all u, v, and ∫ ‖x‖² dμ < ∞; reason: the integrability conjunct is implied by strong log-concavity (all moments are finite); same instances
--   - reading: d (dimension, unconstrained in the statement) → 1 ≤ d; reason: the paper's standing assumption (§5.1, p.22), as in the published Theorem 6.1
--   - encoding: D a distribution on ℝ^d × {0, 1} with first marginal μ → a probability measure on Space d × ℝ with D.map Prod.fst = μ and labels in {0, 1} D-a.s. (BinaryLabels); reason: Lean representation; same instances
--   - encoding: Pr_{(x,y)∼D}[h(x) ≠ y], Bdry_{r,μ}(h), C_{K,μ}, opt_{K,μ} → outer measures of the sets, no measurability of h or of members of C_{K,μ}; C_{K,μ} carries 0 ≤ K; reason: for measurable sets the same value; the bound on outer measures is the stronger statement; 0 ≤ K changes nothing for K ≥ 1 (the published C_K convention)
--   - reading: "with probability at least 1 − δ" → a measurable event of mass ≥ 1 − δ under the stream law (HighProbability), both guarantees on that one event; reason: the published success-event convention; a stronger conclusion
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Theorem A.2, pp.43–44 (PDF pp.43–44); assumption (22), p.43; the modified learner, §A.1–A.3, pp.44–47

import Definitions.Def_GeoLipLearn_Agnostic_Learner
import Definitions.Def_GeoRobustLearn_Supplement_LogConcaveMarginal
import Definitions.Def_GeoRobustLearn_Supplement_BoundaryVolumeMu

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn.Supplement

open GeoLipLearn.Agnostic

/-- **Theorem A.2** (Conditional extension beyond Gaussian marginals), pp.43–44.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I: Agnostically Learning Adversarially
Robust Classifiers*, manuscript of November 3, 2026 (sha256 8cbf3f52…).

Assume (22). There are one training program `P` (arithmetic, examples and Gaussian draws) and one
deterministic arithmetic-only evaluation program `E` such that for every `α ∈ (0, 1]` there is a
constant `C` (depending on `α` only) such that for every `d ≥ 1`, `K ≥ 1`, `0 < r ≤ 1/K`,
`ε, δ ∈ (0, 1/4)`, every isotropic `α`-strongly log-concave `μ` on `ℝ^d` and every distribution `D`
on `ℝ^d × {0, 1}` with first marginal `μ`: on every stream training on input `[α, K, r, ε, δ]`
halts within `R = robustBound C d K r ε δ` steps with at most `R` samples and a representation of
at most `R` reals, `E` evaluates the returned `h` at every query within `R` steps with values in
`{0, 1}`, and on a measurable event of probability at least `1 − δ`,
`Pr_D[h(x) ≠ y] ≤ opt_{K,μ} + ε` and `Bdry_{r,μ}(h) ≤ CKr`.

**Formalization Note.** As for the published Theorem 6.1: "the modification of Algorithm 2 returns"
is the existence of the programs (with `α` an input, "a known constant"), `O(Kr)` and
`(d+1)^{Õ_α(·)} poly(log 1/δ)` are pinned by `C = C(α)` in `robustBound`, and probabilities of
possibly non-measurable sets are outer measures. The programs see only examples from `D` and
standard Gaussian draws (no density, score or conditional-sampling oracle). `d ≥ 1` is the paper's
standing assumption (§5.1). -/
theorem theorem_A_2 (h22 : PolyApprox22) :
    ∃ (P E : Program),
      Admissible P ∧ Admissible E ∧ ArithmeticGauss P ∧ ArithmeticOnly E ∧ Deterministic E ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∃ C : ℕ, 0 < C ∧
      ∀ (d : ℕ) (K r ε δ : ℝ) (μ : Measure (Space d)) (D : Measure (Space d × ℝ)),
        1 ≤ d → IsotropicSLC α μ → IsProbabilityMeasure D → D.map Prod.fst = μ →
        BinaryLabels D →
        1 ≤ K → 0 < r → r ≤ 1 / K → 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 / 4 →
        let R := robustBound C d K r ε δ
        let h : Streams d → Space d → ℝ := fun ω =>
          hypothesis (d := d) E R (representation (train P d 0 [α, K, r, ε, δ] R ω))
        FormulaBudget E d 0 [α, K, r, ε, δ] P R ∧
        (∀ ω x, h ω x = 0 ∨ h ω x = 1) ∧
        HighProbability (streamLaw D) δ (fun ω =>
          D {z | h ω z.1 ≠ z.2} ≤ optKMu μ K D + ENNReal.ofReal ε ∧
          bdryMu μ r (h ω) ≤ ENNReal.ofReal (C * K * r)) := by sorry

end GeoRobustLearn.Supplement
