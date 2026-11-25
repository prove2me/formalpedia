-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_sub
-- name    : GroundTheory.Global.Elliptic.rectIntegral_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:44.751421+00:00
-- url     : https://prove2.me/theorems/f81a01a8-bd95-4f3d-b990-602af237951b
-- title:
--   Elliptic: rect Integral sub
-- statement:
--   The Elliptic construction uses the rect Integral sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L106-L115

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
variable {z w : ℂ} {f g : ℂ → E}

theorem GroundTheory.Global.Elliptic.rectIntegral_sub (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u - g u) z w = rectIntegral f z w - rectIntegral g z w := by sorry
