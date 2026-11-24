-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_deriv_mul
-- name    : GroundTheory.Automorphic.LineKernel.integral_deriv_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:02.758453+00:00
-- url     : https://prove2.me/theorems/94b59590-620b-4034-a977-cea3e08a62dd
-- title:
--   Line Kernel: integral deriv mul
-- statement:
--   The Line Kernel construction uses the integral deriv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L82-L93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
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
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.integral_deriv_mul {F ψ : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) : ∫ u, deriv F u * ψ u = -∫ u, F u * deriv ψ u := by sorry
