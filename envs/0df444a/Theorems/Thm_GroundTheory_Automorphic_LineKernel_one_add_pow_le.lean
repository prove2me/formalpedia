-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_one_add_pow_le
-- name    : GroundTheory.Automorphic.LineKernel.one_add_pow_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:54.566217+00:00
-- url     : https://prove2.me/theorems/465db8ba-9919-4933-ba86-fa1bffca97db
-- title:
--   Line Kernel: one add pow le
-- statement:
--   The Line Kernel construction uses the one add pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L224-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L224-L235

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

theorem GroundTheory.Automorphic.LineKernel.one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by sorry
