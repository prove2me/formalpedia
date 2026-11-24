-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_Supplement_theorem_2
-- name    : GenEmpLik.Coverage.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:15:18.805002+00:00
-- url     : https://prove2.me/theorems/bf879013-87b3-4400-bc8d-e3a127be013c
-- title:
--   Theorem 2 — uniform expansion for the full compact Lipschitz loss class
-- statement:
--   Let $\xi_0,\xi_1,\ldots$ be iid observations with law $P_0$ on a probability space. Let $X\subset\mathbb R^d$ be compact and let $\ell(x;z)$ be real measurable losses. Suppose $|\ell(x;z)-\ell(y;z)|\le M(z)\|x-y\|$ for a measurable nonnegative $M$, with $E_{P_0}M^2<\infty$ and $E_{P_0}|\ell(x_0;\xi)|^2<\infty$ for some $x_0\in X$. Let $f$ satisfy Assumption A and fix $\rho\ge0$. With $s_n^2(x)$ the sample variance with divisor $n$,
--   $$\sup_{P\ll\widehat P_n:D_f(P\|\widehat P_n)\le\rho/n}E_P\ell(x;\xi)
--   =E_{\widehat P_n}\ell(x;\xi)+\sqrt{\rho s_n^2(x)/n}+\varepsilon_n(x),$$
--   $$\sup_{x\in X}\sqrt n\,|\varepsilon_n(x)|\longrightarrow0\quad\text{in outer probability}.$$
--   The error is the defined difference in the first identity. The estimate applies uniformly to the complete decision class, with no bounded-loss or positive-variance restriction.
--
--   **Formalization Note** The published Assumptions A and B and empirical moments are reused. The Euclidean norm is used; equivalence of norms in finite dimension preserves the square-moment condition. Sample indexing starts at zero and all asymptotics ignore the zero-sample index.
--
--   Differences from the source:
--   - encoding: supremum of the scaled absolute remainder → outer probability of existence of a class member exceeding a positive threshold; reason: strict sup exceedance is equivalent to an existential exceedance; this avoids a default real supremum on an empty or unbounded class
--   - reading: distributions with divergence at most rho/n from the empirical law → sample-indexed probability weights in the published divergence ball; reason: (4a), (15) and (31) specify absolute continuity; tied observations retain separate indices and can be averaged by convexity
--   - encoding: random losses and iid observations → explicit measurability, independence and equality in distribution; reason: random variables in Section 2 are measurable; no measurability is imposed on supremum events
--   - generalization: the observation space in the optimization setup is separable metric → an arbitrary measurable observation space; reason: these results only use measurable losses and sample laws, while the decision space remains finite dimensional
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 7, Theorem 2

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_Supplement_uniformRemainder

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GenEmpLik.Coverage.Supplement

/-- Theorem 2, p. 7: the full compact Lipschitz class, with signed losses
and no positive-variance restriction. The remainder is the actual difference in (10).
The existential exceedance event is equivalent to the uniform sup-norm limit. -/
theorem theorem_2
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (M : Ξ → ℝ)
    (f : ℝ → EReal) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : GenEmpLik.Coverage.AssumptionA f)
    (hB : GenEmpLik.Coverage.AssumptionB X ℓ M)
    (hℓmeas : ∀ x ∈ X, Measurable (ℓ x))
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hℓ2 : ∃ x0 ∈ X, Integrable (fun z => ℓ x0 z ^ 2) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω | ∃ x ∈ X,
      δ < Real.sqrt (n : ℝ) *
        |uniformRemainder f ρ (fun i : Fin n => ℓ x (ξ i ω))|}) atTop (𝓝 0) := by sorry

end GenEmpLik.Coverage.Supplement
