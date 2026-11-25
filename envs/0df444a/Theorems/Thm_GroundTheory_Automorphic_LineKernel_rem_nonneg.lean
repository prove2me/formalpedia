-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_nonneg
-- name    : GroundTheory.Automorphic.LineKernel.rem_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:14.62851+00:00
-- url     : https://prove2.me/theorems/282328fa-9a31-48de-b77f-42da6f8e670b
-- title:
--   Line Kernel: rem nonneg
-- statement:
--   The Line Kernel construction uses the rem nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L206-L209

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

theorem GroundTheory.Automorphic.LineKernel.rem_nonneg {a r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ rem a r t := by sorry
