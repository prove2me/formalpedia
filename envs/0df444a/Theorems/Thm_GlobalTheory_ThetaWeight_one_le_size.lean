-- Prove2me | Theorems.Thm_GlobalTheory_ThetaWeight_one_le_size
-- name    : GlobalTheory.ThetaWeight.one_le_size
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:41:23.209691+00:00
-- url     : https://prove2.me/theorems/4b2aa416-b9e1-54f9-83c1-ffb9b6bea6a8
-- title:
--   Theta Weight: one le size
-- statement:
--   The Theta Weight construction uses the one le size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaWeightData.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaWeightData.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaWeightData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThetaWeight
open Finset
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.ThetaWeight.one_le_size {m : ℤ} (hm : 0 ≤ m) {G : (ι → ℤ) × ℤ} (hG : 0 ≤ G.2) : 1 ≤ size m G := by sorry
