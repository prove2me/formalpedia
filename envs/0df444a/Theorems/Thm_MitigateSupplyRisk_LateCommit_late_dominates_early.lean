-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_late_dominates_early
-- name    : MitigateSupplyRisk.LateCommit.late_dominates_early
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:24.500989+00:00
-- url     : https://prove2.me/theorems/03292179-5a0f-4251-b0c9-47109f567aad
-- title:
--   §4.2.2, p. 497 — late commitment (weakly) dominates early commitment: Π₁*ᴱ ≤ Π₁*ᴸ
-- statement:
--   For any two suppliers (not necessarily similar), the optimal late-commitment profit is at least the optimal early-commitment profit:
--   $$\Pi_1^{*E}=\max_{i=1,2}\ \sup_{a\ge a_i^0}\Pi_{1i}^E(a)\ \le\ \Pi_1^{*L}=\sup_{a_1\ge a_1^0,\ a_2\ge a_2^0}\Pi_1^L(a_1,a_2).$$
--
--   Postponing supplier selection until the improvement outcomes are observed hedges against an improvement failure, so it can never hurt. This is the baseline against which Theorem 5 asks when the inequality is strict.
--
--   **Formalization Note** The paper states this as a sentence of §4.2.2 without a number. Both sides are suprema of nonempty sets that are bounded above, and neither is assumed to be attained.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF p. 9), §4.2.2, first paragraph

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- §4.2.2 (p. 497): late commitment (weakly) dominates early commitment,
`Π₁^{*E} ≤ Π₁^{*L}`, for arbitrary (not necessarily identical) suppliers. -/
theorem late_dominates_early (X : Setting) : X.earlyValue ≤ X.lateValue := by sorry

end MitigateSupplyRisk.LateCommit
