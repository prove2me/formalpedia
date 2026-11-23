-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_nonneg
-- name    : GroundTheory.Automorphic.LineKernel.cutoff_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:54.828+00:00
-- url     : https://prove2.me/theorems/e5d46cd6-73ea-47d9-8ae1-dfdc4376ab0a
-- title:
--   Line Kernel: cutoff nonneg
-- statement:
--   The Line Kernel construction uses the cutoff nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.cutoff_nonneg (r t : ℝ) : 0 ≤ cutoff r t := by sorry
