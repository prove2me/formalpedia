-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_continuous_topRows
-- name    : GlobalTheory.GodementJacquet.TestNearE.continuous_topRows
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:55:37.85044+00:00
-- url     : https://prove2.me/theorems/beea36ea-c271-44d4-a3b5-cb4be24ef8f5
-- title:
--   Test Near E: continuous top Rows
-- statement:
--   The Test Near E construction uses the continuous top Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L15-L16

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.GodementJacquet.TestNearE.continuous_topRows (r t : ℕ) : Continuous (topRows (k := k) r t) := by sorry
