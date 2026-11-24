-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_exists_nhds_one
-- name    : GlobalTheory.GodementJacquet.TestNearE.exists_nhds_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:55:15.097406+00:00
-- url     : https://prove2.me/theorems/4d4609ff-c4b7-4810-9bfe-5fa798f34fd7
-- title:
--   Test Near E: exists nhds one
-- statement:
--   The Test Near E construction uses the exists nhds one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L48-L66

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

theorem GlobalTheory.GodementJacquet.TestNearE.exists_nhds_one (r : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ W ∈ 𝓝 (1 : Matrix (Fin r) (Fin r) k), ∀ g : GL (Fin r) k, g.val ∈ W → g ∈ S := by sorry
