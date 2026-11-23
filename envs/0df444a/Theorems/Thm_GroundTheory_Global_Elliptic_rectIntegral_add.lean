-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_add
-- name    : GroundTheory.Global.Elliptic.rectIntegral_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:34.608031+00:00
-- url     : https://prove2.me/theorems/a53aa10c-35b7-4bc2-b47a-72bb2818465f
-- title:
--   Elliptic: rect Integral add
-- statement:
--   The Elliptic construction uses the rect Integral add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L95-L104

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

theorem GroundTheory.Global.Elliptic.rectIntegral_add (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u + g u) z w = rectIntegral f z w + rectIntegral g z w := by sorry
