-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_lemma_2_1_weak_duality
-- name    : InfoRelax.IdealPenalty.lemma_2_1_weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:09.891114+00:00
-- url     : https://prove2.me/theorems/a6c862d2-832a-4f4c-b0b5-3b2eb266fab5
-- title:
--   Lemma 2.1 (Weak Duality)
-- statement:
--   Let $\alpha_F\in\mathcal A_{\mathbb F}$ be a nonanticipative policy, $z\in\mathcal Z_{\mathbb F}$ a dual feasible penalty, and $\mathbb G$ a relaxation of $\mathbb F$. Assume that $\mathbb E[r(\alpha)]$ exists for every policy $\alpha$. Then
--   $$\mathbb E[r(\alpha_F)]\le\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)].\qquad(4)$$
--
--   Any information relaxation combined with any dual feasible penalty therefore bounds the value of every nonanticipative policy, and hence the optimal value of the primal DP, from above. The statement holds for an arbitrary feasible set of action sequences and an arbitrary total reward.
--
--   **Formalization Note** The supremum is taken in the extended reals.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 3, Lemma 2.1, eq. (4)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Lemma 2.1 (Weak Duality)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 3, eq. (4).

If `α_F ∈ 𝒜_𝔽` and `z ∈ 𝒵_𝔽` are primal and dual feasible and `𝔾` is a relaxation of `𝔽`, then
`𝔼[r(α_F)] ≤ sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`.

**Formalization Note.** General framework of §2.1–§2.2: any feasible set `A`, any total reward
`r`, any measurable action type. `hr` is the standing convention that `𝔼[r(α)]` exists for every
policy; the right side is the `EReal` supremum `dualBound`. -/
theorem lemma_2_1_weak_duality {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set (Fin (T + 1) → X))
    (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ)
    (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies A 𝔽)
    (z : (Fin (T + 1) → X) → Ω → ℝ) (hz : z ∈ dualFeasible μ A 𝔽) :
    ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) ≤ dualBound μ A 𝔾 r z := by sorry

end InfoRelax.IdealPenalty
