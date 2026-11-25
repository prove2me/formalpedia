-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_Model_out_mk
-- name    : GlobalTheory.IdxInt.Model.out_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:03.859804+00:00
-- url     : https://prove2.me/theorems/014b8165-c6f4-4194-91f2-e015af71114a
-- title:
--   Model: out mk
-- statement:
--   The Model construction uses the out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]

theorem GlobalTheory.IdxInt.Model.out_mk {φ : W → ℂ} {B : AddSubgroup W} (h : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (w : W) :
    φ (QuotientAddGroup.mk w : W ⧸ B).out = φ w := by sorry
