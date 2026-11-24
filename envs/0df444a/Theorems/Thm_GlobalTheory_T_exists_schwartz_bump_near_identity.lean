-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_schwartz_bump_near_identity
-- name    : GlobalTheory.T.exists_schwartz_bump_near_identity
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:48.733802+00:00
-- url     : https://prove2.me/theorems/8198fc67-f1a4-4cff-a479-be14338eda56
-- title:
--   T: exists schwartz bump near identity
-- statement:
--   The T construction uses the exists schwartz bump near identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentityStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentityStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_schwartz_bump_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)), IsOpen S → (1 : GL (Fin r) k) ∈ S →
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by sorry
