-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_zero
-- name    : GroundTheory.Automorphic.LineKernel.fourier_KC_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:13.640878+00:00
-- url     : https://prove2.me/theorems/eadfd39b-0f53-409d-93fb-c971a64970b4
-- title:
--   Line Kernel: fourier KC zero
-- statement:
--   The Line Kernel construction uses the fourier KC zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L143-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L143-L143

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

theorem GroundTheory.Automorphic.LineKernel.fourier_KC_zero (ξ : ℝ) : 𝓕 (KC a r 0) ξ = khat (a 0) (r 0) ξ := by sorry
