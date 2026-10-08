-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_theorem_2_2_complementary_slackness
-- name    : InfoRelax.IdealPenalty.theorem_2_2_complementary_slackness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:28.725322+00:00
-- url     : https://prove2.me/theorems/42384d57-b439-46de-9354-81adf5f81695
-- title:
--   Theorem 2.2 (Complementary Slackness)
-- statement:
--   Let $\alpha^*_F\in\mathcal A_{\mathbb F}$ and $z^*\in\mathcal Z_{\mathbb F}$ be primal and dual feasible, with information relaxation $\mathbb G$ of $\mathbb F$, and assume $\mathbb E[r(\alpha)]$ exists for every policy $\alpha$. Then $\alpha^*_F$ is optimal for the primal problem (1) and $z^*$ is optimal for the dual problem (6) if and only if $\mathbb E[z^*(\alpha^*_F)]=0$ and
--   $$\mathbb E[r(\alpha^*_F)-z^*(\alpha^*_F)]=\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z^*(\alpha_G)].\qquad(8)$$
--
--   With an optimal penalty, a nonanticipative policy is optimal in the relaxed problem even though policies that use the extra information are available there.
--
--   **Formalization Note** "Optimal for the primal problem" means $\mathbb E[r(\alpha^*_F)]$ equals the primal value; "optimal for the dual problem" means the dual bound of $z^*$ equals the dual value. Values are extended reals.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 4, Theorem 2.2, eq. (8)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Theorem 2.2 (Complementary Slackness)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 4, eq. (8).

Let `α*_F ∈ 𝒜_𝔽` and `z* ∈ 𝒵_𝔽` be primal and dual feasible, with information relaxation `𝔾`.
They are optimal for their respective problems (`𝔼[r(α*_F)]` is the primal value (1) and the dual
bound of `z*` is the dual value (6)) if and only if `𝔼[z*(α*_F)] = 0` and
`𝔼[r(α*_F) − z*(α*_F)] = sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z*(α_G)]`.

**Formalization Note.** General framework of §2.1–§2.2; values in `EReal`; `hr` is the
integrability convention. "With information relaxation `𝔾`" is `IsRelaxation 𝔽 𝔾`. -/
theorem theorem_2_2_complementary_slackness {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies A 𝔽)
    (z : (Fin (T + 1) → X) → Ω → ℝ) (hz : z ∈ dualFeasible μ A 𝔽) :
    (((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) = primalValue μ A 𝔽 r ∧
        dualBound μ A 𝔾 r z = dualValue μ A 𝔽 𝔾 r) ↔
      (∫ ω, z (α ω) ω ∂μ = 0 ∧
        ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal) = dualBound μ A 𝔾 r z) := by sorry

end InfoRelax.IdealPenalty
