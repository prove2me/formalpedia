-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_ftc_hor
-- name    : GlobalTheory.ResRect.ftc_hor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:45.302063+00:00
-- url     : https://prove2.me/theorems/28d0bd7c-f1a2-4153-a367-b1338652ccf3
-- title:
--   Res Rect: ftc hor
-- statement:
--   The Res Rect construction uses the ftc hor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L59-L67

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

theorem GlobalTheory.ResRect.ftc_hor {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    ∫ x : ℝ in a..b, f (x + c * I) = F (b + c * I) - F (a + c * I) := by sorry
