-- Prove2me | Theorems.Thm_GlobalTheory_LowCasShift_rhoC_bd
-- name    : GlobalTheory.LowCasShift.rhoC_bd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:46.340362+00:00
-- url     : https://prove2.me/theorems/dd45db4e-8fd0-46c1-8f90-cac170eaf78e
-- title:
--   Low Cas Shift: rho C bd
-- statement:
--   The Low Cas Shift construction uses the rho C bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.LowCasShift

theorem GlobalTheory.LowCasShift.rhoC_bd {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by sorry
