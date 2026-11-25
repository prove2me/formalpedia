-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_norm_le_of_support
-- name    : GroundTheory.Automorphic.LineKernel.integral_norm_le_of_support
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:11.93921+00:00
-- url     : https://prove2.me/theorems/255238ef-b3b2-4f50-b515-173ca2942ad8
-- title:
--   Line Kernel: integral norm le of support
-- statement:
--   The Line Kernel construction uses the integral norm le of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L76-L84

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

theorem GroundTheory.Automorphic.LineKernel.integral_norm_le_of_support {f : ℝ → ℂ} (hf : Continuous f) {c D : ℝ} (hc : 0 ≤ c)
    (hs : support f ⊆ Icc 0 c) (hD : ∀ t ∈ Icc 0 c, ‖f t‖ ≤ D) : ∫ t, ‖f t‖ ≤ D * c := by sorry
