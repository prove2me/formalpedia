-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_Model_sum_refine
-- name    : GlobalTheory.IdxInt.Model.sum_refine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:41.549973+00:00
-- url     : https://prove2.me/theorems/8f6d6ba0-4271-5821-b1f1-e85e18c4481d
-- title:
--   Model: sum refine
-- statement:
--   The Model construction uses the sum refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean#L24-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_SumRefinement_sum_refine

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

theorem GlobalTheory.IdxInt.Model.sum_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by sorry
