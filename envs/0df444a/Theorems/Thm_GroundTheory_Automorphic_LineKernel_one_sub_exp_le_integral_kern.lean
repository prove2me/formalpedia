-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_one_sub_exp_le_integral_kern
-- name    : GroundTheory.Automorphic.LineKernel.one_sub_exp_le_integral_kern
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:49.289371+00:00
-- url     : https://prove2.me/theorems/7392e002-d115-4370-8bc1-e801f10c2464
-- title:
--   Line Kernel: one sub exp le integral kern
-- statement:
--   The Line Kernel construction uses the one sub exp le integral kern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L258-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L258-L262

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

theorem GroundTheory.Automorphic.LineKernel.one_sub_exp_le_integral_kern {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    1 - exp (-a * r) ≤ ∫ t, kern a r t := by sorry
