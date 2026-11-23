-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_le_one
-- name    : GroundTheory.Automorphic.LineKernel.norm_fourier_KC_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:58.362804+00:00
-- url     : https://prove2.me/theorems/363e47d8-ff62-4de3-894a-e5d4bfd2f2ed
-- title:
--   Line Kernel: norm fourier KC le one
-- statement:
--   The Line Kernel construction uses the norm fourier KC le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L151-L156

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

theorem GroundTheory.Automorphic.LineKernel.norm_fourier_KC_le_one (n : ℕ) (ξ : ℝ) : ‖𝓕 (KC a r n) ξ‖ ≤ 1 := by sorry
