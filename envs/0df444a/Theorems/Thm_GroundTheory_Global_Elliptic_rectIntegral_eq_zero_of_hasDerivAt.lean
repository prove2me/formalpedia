-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_zero_of_hasDerivAt
-- name    : GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_hasDerivAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:15.186977+00:00
-- url     : https://prove2.me/theorems/46e29bb7-0e3f-4d19-9a3c-8bdf9518b4f5
-- title:
--   Elliptic: rect Integral eq zero of has Deriv At
-- statement:
--   The Elliptic construction uses the rect Integral eq zero of has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L159-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L159-L195

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
variable {z w : ℂ}

theorem GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_hasDerivAt [CompleteSpace E] {F f : ℂ → E}
    (hF : ∀ u ∈ rectBoundary z w, HasDerivAt F (f u) u) (hf : ContinuousOn f (rectBoundary z w)) :
    rectIntegral f z w = 0 := by sorry
