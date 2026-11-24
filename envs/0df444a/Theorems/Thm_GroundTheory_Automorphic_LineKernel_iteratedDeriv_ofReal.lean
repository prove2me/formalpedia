-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_ofReal
-- name    : GroundTheory.Automorphic.LineKernel.iteratedDeriv_ofReal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:05.860791+00:00
-- url     : https://prove2.me/theorems/6091f3f0-b17e-429e-8b1c-8191fe3853dc
-- title:
--   Line Kernel: iterated Deriv of Real
-- statement:
--   The Line Kernel construction uses the iterated Deriv of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L31-L38

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

theorem GroundTheory.Automorphic.LineKernel.iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    iteratedDeriv m (fun t => (f t : ℂ)) = fun t => ((iteratedDeriv m f t : ℝ) : ℂ) := by sorry
