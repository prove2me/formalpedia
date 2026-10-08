-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_corollary_2e
-- name    : MitigateSupplyRisk.Improvement.corollary_2e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:48.426272+00:00
-- url     : https://prove2.me/theorems/95908515-5bac-4e86-b9ec-cfd49501bd1c
-- title:
--   Corollary 2(e), p. 497 (η = 0) — the optimal improvement effort is increasing in the unit revenue r
-- statement:
--   Fix the single-supplier model with no committed cost, $\eta = 0$, and the improvement data, and write $\Pi_1^{r}$ for the first-stage profit (7) when the unit revenue is $r$. Let $r_1 \le r_2$, assume the standing assumptions of the model hold at revenue $r_1$ (then they hold at $r_2$), and let $a_1 \ge a^0$ maximize $\Pi_1^{r_1}$ and $a_2 \ge a^0$ maximize $\Pi_1^{r_2}$ over $[a^0,\infty)$. Then
--   $$\max\{a_1, a_2\} \text{ maximizes } \Pi_1^{r_2} \quad\text{and}\quad \min\{a_1, a_2\} \text{ maximizes } \Pi_1^{r_1}$$
--   over $[a^0, \infty)$: the optimal reliability index, and hence the optimal effort, increases in the unit revenue in the strong set order.
--
--   A more valuable product makes supply disruptions costlier and so justifies more improvement effort.
--
--   **Formalization Note** Stated in the strong set order on the argmax, as for Corollary 2(a), and in the setting $\eta = 0$ of Theorem 3. The standing assumptions are required at the lower revenue $r_1$; the only one that involves $r$, $v < r + p$, then also holds at $r_2$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF 9), Corollary 2(e)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem corollary_2e (M : Model) (I : Effort) (hI : I.Assumptions)
    (hη : M.η = 0) (r₁ r₂ : ℝ) (hr : r₁ ≤ r₂)
    (hM₁ : ({ M with r := r₁ } : Model).Assumptions) (a₁ a₂ : ℝ)
    (ha₁ : a₁ ∈ Ici I.a0) (h₁ : IsMaxOn (Pi1 { M with r := r₁ } I) (Ici I.a0) a₁)
    (ha₂ : a₂ ∈ Ici I.a0) (h₂ : IsMaxOn (Pi1 { M with r := r₂ } I) (Ici I.a0) a₂) :
    IsMaxOn (Pi1 { M with r := r₂ } I) (Ici I.a0) (max a₁ a₂) ∧
    IsMaxOn (Pi1 { M with r := r₁ } I) (Ici I.a0) (min a₁ a₂) := by sorry

end MitigateSupplyRisk.Improvement
