-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_notMem_rectBoundary_of_mem_Ioo
-- name    : GroundTheory.Global.Elliptic.notMem_rectBoundary_of_mem_Ioo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:26.387399+00:00
-- url     : https://prove2.me/theorems/123d128d-410c-40e3-90dd-ae1400d73622
-- title:
--   Elliptic: not Mem rect Boundary of mem Ioo
-- statement:
--   The Elliptic construction uses the not Mem rect Boundary of mem Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L50-L61

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

theorem GroundTheory.Global.Elliptic.notMem_rectBoundary_of_mem_Ioo {p : ℂ}
    (hre : p.re ∈ Ioo (min z.re w.re) (max z.re w.re))
    (him : p.im ∈ Ioo (min z.im w.im) (max z.im w.im)) : p ∉ rectBoundary z w := by sorry
