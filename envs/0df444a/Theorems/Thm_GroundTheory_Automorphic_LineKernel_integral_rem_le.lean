-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_rem_le
-- name    : GroundTheory.Automorphic.LineKernel.integral_rem_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:17.890007+00:00
-- url     : https://prove2.me/theorems/a9851996-e28c-4db3-9c33-5297161d1ac1
-- title:
--   Line Kernel: integral rem le
-- statement:
--   The Line Kernel construction uses the integral rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L226-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L226-L244

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

theorem GroundTheory.Automorphic.LineKernel.integral_rem_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) : ∫ t, rem a r t ≤ exp (-a * r) := by sorry
