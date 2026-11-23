-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_ge
-- name    : GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:14.342463+00:00
-- url     : https://prove2.me/theorems/590c6ce4-250c-48c1-871d-8443870e9bd9
-- title:
--   Line Kernel: kern eq zero of ge
-- statement:
--   The Line Kernel construction uses the kern eq zero of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L67-L68

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

theorem GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_ge {a r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ t) : kern a r t = 0 := by sorry
