-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_fourier_KC_succ
-- name    : GroundTheory.Automorphic.LineKernel.fourier_KC_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:35.59544+00:00
-- url     : https://prove2.me/theorems/756ce938-dbb1-44f5-912e-bf6f17bcd1c0
-- title:
--   Line Kernel: fourier KC succ
-- statement:
--   The Line Kernel construction uses the fourier KC succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L145-L149

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

theorem GroundTheory.Automorphic.LineKernel.fourier_KC_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (KC a r (n + 1)) ξ = 𝓕 (KC a r n) ξ * khat (a (n + 1)) (r (n + 1)) ξ := by sorry
