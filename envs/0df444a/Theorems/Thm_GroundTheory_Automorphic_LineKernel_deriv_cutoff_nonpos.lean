-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_deriv_cutoff_nonpos
-- name    : GroundTheory.Automorphic.LineKernel.deriv_cutoff_nonpos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:03.339298+00:00
-- url     : https://prove2.me/theorems/14e4ada7-3bcc-4cef-9684-17cef5d860a7
-- title:
--   Line Kernel: deriv cutoff nonpos
-- statement:
--   The Line Kernel construction uses the deriv cutoff nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L203-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L203-L204

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

theorem GroundTheory.Automorphic.LineKernel.deriv_cutoff_nonpos {r : ℝ} (hr : 0 < r) (t : ℝ) : deriv (cutoff r) t ≤ 0 := by sorry
