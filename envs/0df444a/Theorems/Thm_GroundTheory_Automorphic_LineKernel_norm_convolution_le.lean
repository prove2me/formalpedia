-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_convolution_le
-- name    : GroundTheory.Automorphic.LineKernel.norm_convolution_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:47.208589+00:00
-- url     : https://prove2.me/theorems/f4218f53-1b66-41a8-abed-3112c4eec09a
-- title:
--   Line Kernel: norm convolution le
-- statement:
--   The Line Kernel construction uses the norm convolution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L40-L48

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

theorem GroundTheory.Automorphic.LineKernel.norm_convolution_le {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by sorry
