-- Prove2me | Theorems.Thm_GlobalTheory_ResRect_bdInt_sum
-- name    : GlobalTheory.ResRect.bdInt_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:38.90896+00:00
-- url     : https://prove2.me/theorems/e891ea8d-3c43-42b0-a495-ffb6fab8306e
-- title:
--   Res Rect: bd Int sum
-- statement:
--   The Res Rect construction uses the bd Int sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean#L35-L45

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

theorem GlobalTheory.ResRect.bdInt_sum {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {ι : Type*} (S : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) B) :
    bdInt a b c d (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, bdInt a b c d (f i) := by sorry
