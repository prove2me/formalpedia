-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_abs_pow_mul_norm_fourier_KC_le
-- name    : GroundTheory.Automorphic.LineKernel.abs_pow_mul_norm_fourier_KC_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:32.536397+00:00
-- url     : https://prove2.me/theorems/30c792be-a8ac-4945-a8d4-612b9dca9d5e
-- title:
--   Line Kernel: abs pow mul norm fourier KC le
-- statement:
--   The Line Kernel construction uses the abs pow mul norm fourier KC le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L168-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L168-L189

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

theorem GroundTheory.Automorphic.LineKernel.abs_pow_mul_norm_fourier_KC_le (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (KC a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by sorry
