-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_hform_dblGram
-- name    : GlobalTheory.Doubling.hform_dblGram
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:20.435431+00:00
-- url     : https://prove2.me/theorems/a662d72c-58d7-4ae7-9cf1-1487417bd650
-- title:
--   Doubling: hform dbl Gram
-- statement:
--   The Doubling construction uses the hform dbl Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L215-L217

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
variable [Fintype n] [Fintype ι]

theorem GlobalTheory.Doubling.hform_dblGram (σ : A →+* A) (J : Matrix n n A) (x y x' y' : n → A) :
    hform σ (dblGram e J) (pairVec e x y) (pairVec e x' y') = hform σ J x x' - hform σ J y y' := by sorry
