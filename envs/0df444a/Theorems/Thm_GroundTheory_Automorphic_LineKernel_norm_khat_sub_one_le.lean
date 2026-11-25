-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_khat_sub_one_le
-- name    : GroundTheory.Automorphic.LineKernel.norm_khat_sub_one_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:38.474722+00:00
-- url     : https://prove2.me/theorems/78b3c27d-b12b-4e75-b791-aec35940ae7e
-- title:
--   Line Kernel: norm khat sub one le
-- statement:
--   The Line Kernel construction uses the norm khat sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L335-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L335-L382

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

theorem GroundTheory.Automorphic.LineKernel.norm_khat_sub_one_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) :
    ‖khat a r ξ - 1‖ ≤ 4 * π * r * |ξ| + exp (-a * r) := by sorry
