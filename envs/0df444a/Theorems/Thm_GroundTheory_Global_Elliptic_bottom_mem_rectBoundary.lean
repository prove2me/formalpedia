-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_bottom_mem_rectBoundary
-- name    : GroundTheory.Global.Elliptic.bottom_mem_rectBoundary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:04.672367+00:00
-- url     : https://prove2.me/theorems/c6919177-2e5d-4a0a-9512-977b57563480
-- title:
--   Elliptic: bottom mem rect Boundary
-- statement:
--   The Elliptic construction uses the bottom mem rect Boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L25-L27

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

theorem GroundTheory.Global.Elliptic.bottom_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + z.im * I ∈ rectBoundary z w := by sorry
