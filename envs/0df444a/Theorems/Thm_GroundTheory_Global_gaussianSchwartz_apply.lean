-- Prove2me | Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- name    : GroundTheory.Global.gaussianSchwartz_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:22.853699+00:00
-- url     : https://prove2.me/theorems/4e66ac2c-875d-4e78-aff4-7f6f8a999592
-- title:
--   Global: gaussian Schwartz apply
-- statement:
--   The Global construction uses the gaussian Schwartz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianSchwartz.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianSchwartz.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Real Function
open scoped ContDiff Nat SchwartzMap
open GroundTheory GroundTheory.Global
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem GroundTheory.Global.gaussianSchwartz_apply (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) := by sorry

attribute [defeq] GroundTheory.Global.gaussianSchwartz_apply
