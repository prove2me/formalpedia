-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_add_integral_rem
-- name    : GroundTheory.Automorphic.LineKernel.integral_kern_add_integral_rem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:06.16185+00:00
-- url     : https://prove2.me/theorems/508c3058-1055-4996-b5d9-faf06cd188d4
-- title:
--   Line Kernel: integral kern add integral rem
-- statement:
--   The Line Kernel construction uses the integral kern add integral rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L246-L251

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

theorem GroundTheory.Automorphic.LineKernel.integral_kern_add_integral_rem {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t, kern a r t) + ∫ t, rem a r t = 1 := by sorry
