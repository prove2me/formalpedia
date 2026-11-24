-- Prove2me | Theorems.Thm_GlobalTheory_Hk_integral_ellipse_width
-- name    : GlobalTheory.Hk.integral_ellipse_width
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:15.630723+00:00
-- url     : https://prove2.me/theorems/c8790358-a1e1-442a-b3ac-4cf9e9f6ed1a
-- title:
--   Hk: integral ellipse width
-- statement:
--   The Hk construction uses the integral ellipse width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L147-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L147-L174

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

theorem GlobalTheory.Hk.integral_ellipse_width (α γ x a b : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hx : 0 < x)
    (ha : a ≤ -Real.sqrt (x / γ)) (hb : Real.sqrt (x / γ) ≤ b) :
    ∫ t in a..b, 2 * Real.sqrt ((x - γ * t ^ 2) / α) = Real.pi / Real.sqrt (α * γ) * x := by sorry
