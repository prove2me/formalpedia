-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_topRows_eMat
-- name    : GlobalTheory.GodementJacquet.TestNearE.topRows_eMat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:06.152905+00:00
-- url     : https://prove2.me/theorems/6dc660fe-39e6-414c-8c72-df4828573e6c
-- title:
--   Test Near E: top Rows e Mat
-- statement:
--   The Test Near E construction uses the top Rows e Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L23-L24

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

theorem GlobalTheory.GodementJacquet.TestNearE.topRows_eMat (r t : ℕ) : topRows r t (eMat k r t) = 1 := by sorry
