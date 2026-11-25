-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_mul_of_support
-- name    : GroundTheory.Automorphic.LineKernel.integrable_mul_of_support
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:25.686824+00:00
-- url     : https://prove2.me/theorems/abda4883-6b74-443f-8429-616b4bb1251c
-- title:
--   Line Kernel: integrable mul of support
-- statement:
--   The Line Kernel construction uses the integrable mul of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L86-L94

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

theorem GroundTheory.Automorphic.LineKernel.integrable_mul_of_support {φ K : ℝ → ℂ} (hφ : Continuous φ) (hK : Integrable K) {c : ℝ}
    (hs : support K ⊆ Icc 0 c) : Integrable fun u => φ u * K u := by sorry
