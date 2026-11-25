-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_Fubini_cint_prod
-- name    : GlobalTheory.IdxInt.Fubini.cint_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:22.429483+00:00
-- url     : https://prove2.me/theorems/784e9ebe-04b5-43c8-92f3-cd8ed13ff42a
-- title:
--   Fubini: cint prod
-- statement:
--   The Fubini construction uses the cint prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralProdFubini.lean#L45-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralProdFubini.lean#L45-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Fubini
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

theorem GlobalTheory.IdxInt.Fubini.cint_prod (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by sorry
