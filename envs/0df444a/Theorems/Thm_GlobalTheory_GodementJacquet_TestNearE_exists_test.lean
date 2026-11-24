-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_exists_test
-- name    : GlobalTheory.GodementJacquet.TestNearE.exists_test
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:03.204849+00:00
-- url     : https://prove2.me/theorems/a72fdcac-c49c-424c-969e-3de9fa3343db
-- title:
--   Test Near E: exists test
-- statement:
--   The Test Near E construction uses the exists test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L88-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L88-L138

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

theorem GlobalTheory.GodementJacquet.TestNearE.exists_test (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin r) k) ∈ S) :
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by sorry
