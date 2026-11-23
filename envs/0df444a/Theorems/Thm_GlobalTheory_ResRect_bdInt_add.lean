-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_bdInt_add
-- name    : GlobalTheory.ResRect.bdInt_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:46.400718+00:00
-- url     : https://prove2.me/theorems/e7ea0e2f-732c-4490-9ff0-98bad0b17965
-- title:
--   Res Rect: bd Int add
-- statement:
--   The Res Rect construction uses the bd Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L24-L33

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

theorem GlobalTheory.ResRect.bdInt_add {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hf : ContinuousOn f B) (hg : ContinuousOn g B) :
    bdInt a b c d (fun s => f s + g s) = bdInt a b c d f + bdInt a b c d g := by sorry
