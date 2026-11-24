-- Prove2me | Theorems.Thm_GlobalTheory_sq_intervalIntegral_le_mul_intervalIntegral_sq
-- name    : GlobalTheory.sq_intervalIntegral_le_mul_intervalIntegral_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:32.609398+00:00
-- url     : https://prove2.me/theorems/821e6071-bee0-48d0-8bbc-31cfb9b5b4e9
-- title:
--   Global Theory: sq interval Integral le mul interval Integral sq
-- statement:
--   The Global Theory construction uses the sq interval Integral le mul interval Integral sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqIntervalIntegralLeMulIntervalIntegralSq.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqIntervalIntegralLeMulIntervalIntegralSq.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by sorry
