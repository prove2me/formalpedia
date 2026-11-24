-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_zero_of_differentiable_on_off_countable
-- name    : GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_differentiable_on_off_countable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:41.789801+00:00
-- url     : https://prove2.me/theorems/b9237780-2d20-472e-8f45-c10da61a3b0c
-- title:
--   Elliptic: rect Integral eq zero of differentiable on off countable
-- statement:
--   The Elliptic construction uses the rect Integral eq zero of differentiable on off countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L313-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L313-L319

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_differentiable_on_off_countable [CompleteSpace E] (f : ℂ → E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 := by sorry
