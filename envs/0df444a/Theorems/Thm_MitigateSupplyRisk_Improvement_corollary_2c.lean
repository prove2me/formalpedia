-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_corollary_2c
-- name    : MitigateSupplyRisk.Improvement.corollary_2c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:43.117161+00:00
-- url     : https://prove2.me/theorems/bf4b4b14-2165-4f3d-b3b6-7bdc02f91619
-- title:
--   Corollary 2(c), p. 497 (η = 0) — the optimal improvement effort is decreasing in the unit procurement cost c
-- statement:
--   Fix the single-supplier model with no committed cost, $\eta = 0$, and the improvement data, and write $\Pi_1^{c}$ for the first-stage profit (7) when the supplier's unit cost is $c$. Let $c_1 \le c_2$, let $a_1 \ge a^0$ maximize $\Pi_1^{c_1}$ and $a_2 \ge a^0$ maximize $\Pi_1^{c_2}$ over $[a^0,\infty)$. Then
--   $$\max\{a_1, a_2\} \text{ maximizes } \Pi_1^{c_1} \quad\text{and}\quad \min\{a_1, a_2\} \text{ maximizes } \Pi_1^{c_2}$$
--   over $[a^0, \infty)$: the optimal reliability index, and hence the optimal effort, decreases in the unit procurement cost in the strong set order.
--
--   A cheaper supplier is worth improving more, because each unit its improved capacity delivers earns a larger margin.
--
--   **Formalization Note** Stated in the strong set order on the argmax, as for Corollary 2(a). It is stated in the setting of Theorem 3, $\eta = 0$, which immediately precedes the corollary; the case $\eta > 0$ is not covered by this item.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF 9), Corollary 2(c)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem corollary_2c (M : Model) (I : Effort) (hM : M.Assumptions) (hI : I.Assumptions)
    (hη : M.η = 0) (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) (a₁ a₂ : ℝ)
    (ha₁ : a₁ ∈ Ici I.a0) (h₁ : IsMaxOn (Pi1 { M with c := c₁ } I) (Ici I.a0) a₁)
    (ha₂ : a₂ ∈ Ici I.a0) (h₂ : IsMaxOn (Pi1 { M with c := c₂ } I) (Ici I.a0) a₂) :
    IsMaxOn (Pi1 { M with c := c₁ } I) (Ici I.a0) (max a₁ a₂) ∧
    IsMaxOn (Pi1 { M with c := c₂ } I) (Ici I.a0) (min a₁ a₂) := by sorry

end MitigateSupplyRisk.Improvement
