-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_eq_zero
-- name    : GroundTheory.Automorphic.LineKernel.rem_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:22.797134+00:00
-- url     : https://prove2.me/theorems/7f6faa1e-dccf-4fd3-aa41-3655e3151c18
-- title:
--   Line Kernel: rem eq zero
-- statement:
--   The Line Kernel construction uses the rem eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L112-L115

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

theorem GroundTheory.Automorphic.LineKernel.rem_eq_zero {a r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc r (2 * r)) : rem a r t = 0 := by sorry
