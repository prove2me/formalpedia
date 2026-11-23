-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_one
-- name    : GroundTheory.Automorphic.LineKernel.cutoff_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:54.149693+00:00
-- url     : https://prove2.me/theorems/54de1d6d-306b-45e1-b360-19ffe9d3a1af
-- title:
--   Line Kernel: cutoff eq one
-- statement:
--   The Line Kernel construction uses the cutoff eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L19-L22

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

theorem GroundTheory.Automorphic.LineKernel.cutoff_eq_one {r t : ℝ} (hr : 0 < r) (ht : t ≤ r) : cutoff r t = 1 := by sorry
