-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_Model_supp_fin
-- name    : GlobalTheory.IdxInt.Model.supp_fin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:39.88515+00:00
-- url     : https://prove2.me/theorems/97197a63-b139-522a-9f37-865bf7be0977
-- title:
--   Model: supp fin
-- statement:
--   The Model construction uses the supp fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L18-L22

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

theorem GlobalTheory.IdxInt.Model.supp_fin {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    (Function.support fun c : W ⧸ B => φ c.out).Finite := by sorry
