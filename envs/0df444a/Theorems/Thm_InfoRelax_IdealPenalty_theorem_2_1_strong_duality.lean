-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_theorem_2_1_strong_duality
-- name    : InfoRelax.IdealPenalty.theorem_2_1_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:34.660781+00:00
-- url     : https://prove2.me/theorems/f93bbd78-cbc5-40f9-8e3a-cd832cfe20dd
-- title:
--   Theorem 2.1 (Strong Duality)
-- statement:
--   Let $\mathbb G$ be a relaxation of the natural filtration $\mathbb F$, let the feasible set $A$ be nonempty, and assume $\mathbb E[r(\alpha)]$ exists for every policy $\alpha$. Then
--   $$\sup_{\alpha_F\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha_F)]=\inf_{z\in\mathcal Z_{\mathbb F}}\Big\{\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)]\Big\}.\qquad(7)$$
--   Furthermore, if the primal value on the left is finite (the primal problem is bounded), the dual problem on the right has an optimal solution $z^*\in\mathcal Z_{\mathbb F}$ whose dual bound equals the primal value.
--
--   This is the analogue of the strong duality theorem of linear programming: there is no gap between the primal DP and its information-relaxation dual.
--
--   **Formalization Note** Both sides are in the extended reals, so (7) is asserted also when the primal value is $+\infty$. "Bounded" means the primal value is not $+\infty$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 4, Theorem 2.1, eq. (7)

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **Theorem 2.1 (Strong Duality)**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 4, eq. (7).

Let `𝔾` be a relaxation of `𝔽`. Then
`sup_{α_F ∈ 𝒜_𝔽} 𝔼[r(α_F)] = inf_{z ∈ 𝒵_𝔽} sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`.
Furthermore, if the primal problem is bounded, the dual problem has an optimal solution
`z* ∈ 𝒵_𝔽` that achieves this bound.

**Formalization Note.** General framework of §2.1–§2.2. Values in `EReal`; (7) is stated also when
the primal value is `+∞`. "The primal problem is bounded" is `primalValue ≠ ⊤`; "achieves this
bound" is `dualBound 𝔾 z* = primalValue` (which, by (7), is the dual value). `A.Nonempty` is the
page's tacit assumption; `hr` is the integrability convention. -/
theorem theorem_2_1_strong_duality {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set (Fin (T + 1) → X))
    (hA : A.Nonempty) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ)
    (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾) :
    primalValue μ A 𝔽 r = dualValue μ A 𝔽 𝔾 r ∧
      (primalValue μ A 𝔽 r ≠ ⊤ →
        ∃ z ∈ dualFeasible μ A 𝔽, dualBound μ A 𝔾 r z = primalValue μ A 𝔽 r) := by sorry

end InfoRelax.IdealPenalty
