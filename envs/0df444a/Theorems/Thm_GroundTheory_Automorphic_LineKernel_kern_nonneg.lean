-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_nonneg
-- name    : GroundTheory.Automorphic.LineKernel.kern_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:18.890242+00:00
-- url     : https://prove2.me/theorems/392250b8-7057-4189-a8f4-b2ba82640180
-- title:
--   Line Kernel: kern nonneg
-- statement:
--   The Line Kernel construction uses the kern nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L58-L62

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

theorem GroundTheory.Automorphic.LineKernel.kern_nonneg {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : 0 ≤ kern a r t := by sorry
