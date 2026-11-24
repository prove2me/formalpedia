-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_succ_sub_le
-- name    : GroundTheory.Automorphic.LineKernel.norm_fourier_KC_succ_sub_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:12.131001+00:00
-- url     : https://prove2.me/theorems/6c8dae01-c30a-4bae-839e-23be8293dc79
-- title:
--   Line Kernel: norm fourier KC succ sub le
-- statement:
--   The Line Kernel construction uses the norm fourier KC succ sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L158-L166

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

theorem GroundTheory.Automorphic.LineKernel.norm_fourier_KC_succ_sub_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (KC a r (n + 1)) ξ - 𝓕 (KC a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by sorry
