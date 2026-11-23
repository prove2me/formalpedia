-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_le_one
-- name    : GroundTheory.Automorphic.LineKernel.integral_kern_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:52.008204+00:00
-- url     : https://prove2.me/theorems/1b0d942c-8d01-4ede-a90f-d7be7e77b629
-- title:
--   Line Kernel: integral kern le one
-- statement:
--   The Line Kernel construction uses the integral kern le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L253-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L253-L256

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

theorem GroundTheory.Automorphic.LineKernel.integral_kern_le_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : ∫ t, kern a r t ≤ 1 := by sorry
