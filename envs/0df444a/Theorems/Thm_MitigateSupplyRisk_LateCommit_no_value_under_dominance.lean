-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_no_value_under_dominance
-- name    : MitigateSupplyRisk.LateCommit.no_value_under_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:49.886934+00:00
-- url     : https://prove2.me/theorems/a2e31e30-13c4-49ff-9ac8-d2f5b5a08e8b
-- title:
--   §4.2.2, p. 498 — Π₁*ᴸ = Π₁*ᴱ if Π₂*(a_i^{*E}) < Π₂*(a_j^0): no value of late commitment under dominance
-- statement:
--   Let $j$ denote the supplier other than $i$. Suppose that for $i=1$ or $i=2$ there is a maximizer $a_i^{*E}\ge a_i^0$ of supplier $i$'s early-commitment profit $\Pi_{1i}^E$ over $a\ge a_i^0$ such that
--   $$P_i(a_i^{*E})<P_j(a_j^0),$$
--   where $P_k$ is supplier $k$'s single-sourcing value $\Pi_2^*$. Then late commitment offers no value:
--   $$\Pi_1^{*L}=\Pi_1^{*E}.$$
--
--   In words: if one supplier at its current reliability is preferred over the other supplier at that supplier's optimal early-commitment reliability, the optimal selection does not depend on improvement outcomes, so postponing it is worthless.
--
--   **Formalization Note** The paper states this as a consequence of Lemma 4 and (9) without a number. $\Pi_1^{*L}$ and $\Pi_1^{*E}$ are suprema, not assumed to be attained. Only the early maximizer of supplier $i$ is assumed to exist.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 498 (PDF p. 10), §4.2.2, paragraph after Lemma 4

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- §4.2.2 (p. 498): `Π₁^{*L} = Π₁^{*E}` if `Π₂*(aᵢ^{*E}) < Π₂*(aⱼ⁰)` for `i = 1` or `i = 2`
(`j` the other supplier), where `aᵢ^{*E}` is a maximizer of supplier `i`'s early-commitment
profit over `aᵢ ≥ aᵢ⁰`. -/
theorem no_value_under_dominance (X : Setting)
    (h : (∃ a₁E, X.I₁.a0 ≤ a₁E ∧ IsMaxOn X.early₁ (Set.Ici X.I₁.a0) a₁E ∧
            X.P₁ a₁E < X.P₂ X.I₂.a0) ∨
         (∃ a₂E, X.I₂.a0 ≤ a₂E ∧ IsMaxOn X.early₂ (Set.Ici X.I₂.a0) a₂E ∧
            X.P₂ a₂E < X.P₁ X.I₁.a0)) :
    X.lateValue = X.earlyValue := by sorry

end MitigateSupplyRisk.LateCommit
