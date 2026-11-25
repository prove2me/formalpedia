-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_neg
-- name    : GroundTheory.Global.Elliptic.rectIntegral_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:47.574381+00:00
-- url     : https://prove2.me/theorems/d79f9108-507e-4be4-a919-51d591de09d8
-- title:
--   Elliptic: rect Integral neg
-- statement:
--   The Elliptic construction uses the rect Integral neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L117-L119

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

theorem GroundTheory.Global.Elliptic.rectIntegral_neg : rectIntegral (fun u ↦ -f u) z w = -rectIntegral f z w := by sorry
