-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_1
-- name    : HindsightGain.Uniform.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:37.800415+00:00
-- url     : https://prove2.me/theorems/06dd14ac-853c-4343-a8d5-55c083a24bcb
-- title:
--   Theorem 1 — Independent weights: $0\le\mathrm{Gap}_A(\zeta)\le r\sqrt5\,\|A\|_F M^{(r-1)/2}\sigma_{\max}$
-- statement:
--   Let $(K,A)$ be an instance of the model of Section 1.1: $n,D\ge1$, $r\ge2$, nonempty compact local domains $K_i$ in the Euclidean unit ball of $\mathbb R^D$, and arbitrary $r$-variable multilinear interactions $A_e$. Let $\zeta_1,\dots,\zeta_n$ be independent nonnegative random variables with finite second moments, and put $M=\sum_i\mathbb E\zeta_i^2$, $\sigma_{\max}=\max_i\sqrt{\mathrm{Var}(\zeta_i)}$ and $\|A\|_F^2=\sum_e\|A_e\|_F^2$, where $\|A_e\|_F$ is the Frobenius norm of the coefficient array of $A_e$. Then $\mathrm{Val}_A(\zeta)$ is integrable and
--   $$0\le\mathrm{Gap}_A(\zeta)\le r\sqrt5\,\|A\|_F\,M^{(r-1)/2}\,\sigma_{\max}.$$
--
--   The bound is dimension-free: it depends only on the coefficient norm, the degree and two moment parameters, and it needs only second moments of the weights. It is a companion result of the mission's goal, which sharpens the Bernoulli case.
--
--   **Formalization Note** The model is the published `Model`; $\mathrm{Gap}$, $M$ and $\sigma_{\max}$ are the concrete source quantities.
--
--   Differences from the source:
--   - encoding: independent nonnegative random variables with finite second moments → an iIndepFun family on an arbitrary probability space, almost surely nonnegative, in L²; reason: random variables are identified up to null sets; L² is the finite-second-moment condition
--   - encoding: the expectation E Val_A(ζ), shown finite on p.13 → integrability of Val_A(ζ) asserted as a conjunct of the conclusion; reason: the Bochner integral is 0 for a non-integrable function, so finiteness is stated and proved rather than assumed
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 1, p.18 (also stated p.4); integrability p.13

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_weights

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- Theorem 1, p.18 (also p.4): independent nonnegative weights with finite second moments, on an
arbitrary probability space. Integrability of the weighted optimum (shown on p.13) is part of the
conclusion, so the expectation in `Gap_A(ζ)` is a genuine one. -/
theorem theorem_1 {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Fin n → Ω → ℝ) (hindep : iIndepFun ζ μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ ζ i ω) (hsecond : ∀ i, MemLp (ζ i) 2 μ) :
    Integrable (fun ω => val M (fun i => ζ i ω)) μ ∧
      0 ≤ gap M μ ζ ∧
      gap M μ ζ ≤ (r : ℝ) * Real.sqrt 5 * frobenius M *
        secondMomentSum μ ζ ^ (((r : ℝ) - 1) / 2) * sigmaMax μ ζ := by sorry

end HindsightGain.Uniform.Supplement
