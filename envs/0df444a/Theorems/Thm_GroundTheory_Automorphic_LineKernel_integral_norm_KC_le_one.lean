-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_norm_KC_le_one
-- name    : GroundTheory.Automorphic.LineKernel.integral_norm_KC_le_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:26.473944+00:00
-- url     : https://prove2.me/theorems/0df33cda-c94e-4343-b24b-8f221027efa2
-- title:
--   Line Kernel: integral norm KC le one
-- statement:
--   The Line Kernel construction uses the integral norm KC le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
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
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem GroundTheory.Automorphic.LineKernel.integral_norm_KC_le_one (n : ℕ) : ∫ t, ‖KC a r n t‖ ≤ 1 := by sorry
