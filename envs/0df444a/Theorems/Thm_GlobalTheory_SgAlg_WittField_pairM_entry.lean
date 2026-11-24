-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_pairM_entry
-- name    : GlobalTheory.SgAlg.WittField.pairM_entry
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:13.249886+00:00
-- url     : https://prove2.me/theorems/dffd51a5-ab71-42d5-a758-e73d8acf6753
-- title:
--   Witt Field: pair M entry
-- statement:
--   The Witt Field construction uses the pair M entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L221-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L221-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.SgAlg.WittField.pairM_entry {a : ℕ} (X : Matrix (Fin n) (Fin a) E) (i j : Fin a) :
    pairM σ J X X i j = form σ J (fun k => X k j) (fun k => X k i) := by sorry
