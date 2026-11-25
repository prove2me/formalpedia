-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_const_mul
-- name    : GroundTheory.Global.Elliptic.rectIntegral_const_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:38.92924+00:00
-- url     : https://prove2.me/theorems/f9cc19a2-1ac0-4b45-a6f1-558762ba835c
-- title:
--   Elliptic: rect Integral const mul
-- statement:
--   The Elliptic construction uses the rect Integral const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L125-L127

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

theorem GroundTheory.Global.Elliptic.rectIntegral_const_mul {f : ℂ → ℂ} (c : ℂ) :
    rectIntegral (fun u ↦ c * f u) z w = c * rectIntegral f z w := by sorry
