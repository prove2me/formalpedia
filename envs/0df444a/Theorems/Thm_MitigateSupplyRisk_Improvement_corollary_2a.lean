-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_corollary_2a
-- name    : MitigateSupplyRisk.Improvement.corollary_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:54.008696+00:00
-- url     : https://prove2.me/theorems/d52265af-4723-4719-818f-4f8c081258c4
-- title:
--   Corollary 2(a), p. 497 — the optimal improvement effort is decreasing in the improvement cost m
-- statement:
--   Fix the single-supplier model and the improvement data except the unit effort cost, and write $\Pi_1^{m}$ for the first-stage profit (7) with unit effort cost $m$. Let $0 \le m_1 \le m_2$, let $a_1 \ge a^0$ maximize $\Pi_1^{m_1}$ over $[a^0,\infty)$ and let $a_2 \ge a^0$ maximize $\Pi_1^{m_2}$ over $[a^0,\infty)$. Then
--   $$\max\{a_1, a_2\} \text{ maximizes } \Pi_1^{m_1} \quad\text{and}\quad \min\{a_1, a_2\} \text{ maximizes } \Pi_1^{m_2}$$
--   over $[a^0, \infty)$. That is, the set of optimal reliability indices, and hence the optimal effort $z^* = z(a^*)$, decreases in $m$ in the strong set order.
--
--   A more expensive improvement process never makes it optimal to aim for a more reliable supplier.
--
--   **Formalization Note** Optimal indices need not be unique ($\Pi_1$ is concave, not strictly), so "the optimal effort is decreasing in $m$" is stated in the strong set order on the argmax, which is the standard meaning of monotone comparative statics for set-valued optima. The effort ordering follows because $z$ is nondecreasing. The statement holds for every committed cost $\eta$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF 9), Corollary 2(a)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem corollary_2a (M : Model) (I : Effort) (hM : M.Assumptions) (hI : I.Assumptions)
    (m₁ m₂ : ℝ) (hm₁ : 0 ≤ m₁) (hm : m₁ ≤ m₂) (a₁ a₂ : ℝ)
    (ha₁ : a₁ ∈ Ici I.a0) (h₁ : IsMaxOn (Pi1 M { I with m := m₁ }) (Ici I.a0) a₁)
    (ha₂ : a₂ ∈ Ici I.a0) (h₂ : IsMaxOn (Pi1 M { I with m := m₂ }) (Ici I.a0) a₂) :
    IsMaxOn (Pi1 M { I with m := m₁ }) (Ici I.a0) (max a₁ a₂) ∧
    IsMaxOn (Pi1 M { I with m := m₂ }) (Ici I.a0) (min a₁ a₂) := by sorry

end MitigateSupplyRisk.Improvement
