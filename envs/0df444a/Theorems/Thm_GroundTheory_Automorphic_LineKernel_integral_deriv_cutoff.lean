-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_deriv_cutoff
-- name    : GroundTheory.Automorphic.LineKernel.integral_deriv_cutoff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:00.127726+00:00
-- url     : https://prove2.me/theorems/aaf4a011-5d7b-4a67-8867-76b21479aef6
-- title:
--   Line Kernel: integral deriv cutoff
-- statement:
--   The Line Kernel construction uses the integral deriv cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L214-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L214-L224

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

theorem GroundTheory.Automorphic.LineKernel.integral_deriv_cutoff {r : ℝ} (hr : 0 < r) : ∫ t, deriv (cutoff r) t = -1 := by sorry
