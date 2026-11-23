-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_int_ver
-- name    : GlobalTheory.ResRect.int_ver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:23.362187+00:00
-- url     : https://prove2.me/theorems/2cf64b64-6d28-46dc-984a-8496978d57a9
-- title:
--   Res Rect: int ver
-- statement:
--   The Res Rect construction uses the int ver property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L19-L22

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

theorem GlobalTheory.ResRect.int_ver {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d := by sorry
