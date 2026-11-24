-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_bdInt_eq_zero_of_primitive
-- name    : GlobalTheory.ResRect.bdInt_eq_zero_of_primitive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:43.860653+00:00
-- url     : https://prove2.me/theorems/6fd9f5d1-9898-4154-bedd-12b0a23f1ea8
-- title:
--   Res Rect: bd Int eq zero of primitive
-- statement:
--   The Res Rect construction uses the bd Int eq zero of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L82-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect

theorem GlobalTheory.ResRect.bdInt_eq_zero_of_primitive {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B)
    {F f : ℂ → ℂ} (hf : ContinuousOn f B) (hF : ∀ s ∈ B, HasDerivAt F (f s) s) :
    bdInt a b c d f = 0 := by sorry
