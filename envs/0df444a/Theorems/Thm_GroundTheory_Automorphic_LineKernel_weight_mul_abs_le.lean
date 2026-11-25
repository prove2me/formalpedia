-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_mul_abs_le
-- name    : GroundTheory.Automorphic.LineKernel.weight_mul_abs_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:04:22.606383+00:00
-- url     : https://prove2.me/theorems/879c1a77-42d0-44e9-9853-ec12f07a7fd6
-- title:
--   Line Kernel: weight mul abs le
-- statement:
--   The Line Kernel construction uses the weight mul abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L41-L49

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.weight_mul_abs_le (M : ℕ → ℝ) (p : ℕ) :
    weight M p * |M p| ≤ (1 / 2) ^ p * max 1 |M 0| := by sorry
