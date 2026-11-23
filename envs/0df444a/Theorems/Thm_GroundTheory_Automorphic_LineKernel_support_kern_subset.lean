-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_kern_subset
-- name    : GroundTheory.Automorphic.LineKernel.support_kern_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:12.248249+00:00
-- url     : https://prove2.me/theorems/8677b6df-cf41-47a7-88a3-22d77fc9c7d4
-- title:
--   Line Kernel: support kern subset
-- statement:
--   The Line Kernel construction uses the support kern subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L73-L78

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

theorem GroundTheory.Automorphic.LineKernel.support_kern_subset {a r : ℝ} (hr : 0 < r) : support (kern a r) ⊆ Icc 0 (2 * r) := by sorry
