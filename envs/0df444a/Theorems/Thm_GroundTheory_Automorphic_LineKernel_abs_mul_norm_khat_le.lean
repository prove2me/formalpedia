-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_abs_mul_norm_khat_le
-- name    : GroundTheory.Automorphic.LineKernel.abs_mul_norm_khat_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:25.90826+00:00
-- url     : https://prove2.me/theorems/ba2ba347-776d-4746-87c1-4010cb4162cc
-- title:
--   Line Kernel: abs mul norm khat le
-- statement:
--   The Line Kernel construction uses the abs mul norm khat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L280-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L280-L333

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

theorem GroundTheory.Automorphic.LineKernel.abs_mul_norm_khat_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) :
    |ξ| * ‖khat a r ξ‖ ≤ a / π := by sorry
