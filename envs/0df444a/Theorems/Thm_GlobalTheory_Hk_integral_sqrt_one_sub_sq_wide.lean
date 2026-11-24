-- Prove2me | Theorems.Thm_GlobalTheory_Hk_integral_sqrt_one_sub_sq_wide
-- name    : GlobalTheory.Hk.integral_sqrt_one_sub_sq_wide
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:17.441991+00:00
-- url     : https://prove2.me/theorems/1e69a39d-3d2d-457c-a760-b1b17e39bcff
-- title:
--   Hk: integral sqrt one sub sq wide
-- statement:
--   The Hk construction uses the integral sqrt one sub sq wide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L123-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L123-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.integral_sqrt_one_sub_sq_wide (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ t in a..b, Real.sqrt (1 - t ^ 2) = Real.pi / 2 := by sorry
