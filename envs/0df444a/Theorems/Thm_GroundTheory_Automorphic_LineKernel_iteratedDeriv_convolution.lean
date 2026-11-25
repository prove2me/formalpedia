-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_convolution
-- name    : GroundTheory.Automorphic.LineKernel.iteratedDeriv_convolution
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:03.588613+00:00
-- url     : https://prove2.me/theorems/5582b7a1-c47d-48cc-8ec3-71d60920c76e
-- title:
--   Line Kernel: iterated Deriv convolution
-- statement:
--   The Line Kernel construction uses the iterated Deriv convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L30-L38

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

theorem GroundTheory.Automorphic.LineKernel.iteratedDeriv_convolution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by sorry
