-- Prove2me | Theorems.Thm_GlobalTheory_LowCasShift_sqrt_step
-- name    : GlobalTheory.LowCasShift.sqrt_step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:28.104799+00:00
-- url     : https://prove2.me/theorems/c53a40d7-c578-57c8-a9da-2b94b7580dab
-- title:
--   Low Cas Shift: sqrt step
-- statement:
--   The Low Cas Shift construction uses the sqrt step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L57-L65

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

theorem GlobalTheory.LowCasShift.sqrt_step {X Y b : ℝ} (hb : 4 ≤ b) (hX : (b / 2) ^ 2 ≤ X) (hY : X - b ≤ Y) :
    Real.sqrt X ≤ Real.sqrt Y + 2 := by sorry
