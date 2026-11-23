-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasDerivAt_iteratedDeriv
-- name    : GroundTheory.Automorphic.LineKernel.hasDerivAt_iteratedDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:12.409823+00:00
-- url     : https://prove2.me/theorems/1dae8beb-5207-48bf-93a5-25384e82e7d5
-- title:
--   Line Kernel: has Deriv At iterated Deriv
-- statement:
--   The Line Kernel construction uses the has Deriv At iterated Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L25-L29

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.hasDerivAt_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by sorry
