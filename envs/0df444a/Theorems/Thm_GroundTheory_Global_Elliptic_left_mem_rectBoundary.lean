-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_left_mem_rectBoundary
-- name    : GroundTheory.Global.Elliptic.left_mem_rectBoundary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:19.818807+00:00
-- url     : https://prove2.me/theorems/7577e6c6-0cea-4c6e-94e4-477b3f94b617
-- title:
--   Elliptic: left mem rect Boundary
-- statement:
--   The Elliptic construction uses the left mem rect Boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L37-L39

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

theorem GroundTheory.Global.Elliptic.left_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + y * I ∈ rectBoundary z w := by sorry
