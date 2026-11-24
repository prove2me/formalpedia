-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_opT_succ
-- name    : GroundTheory.Automorphic.LineKernel.opT_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:45.694609+00:00
-- url     : https://prove2.me/theorems/626eb3be-c1dd-4d71-9482-4658c06af197
-- title:
--   Line Kernel: op T succ
-- statement:
--   The Line Kernel construction uses the op T succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L171-L174

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

theorem GroundTheory.Automorphic.LineKernel.opT_succ (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) :
    opT a (n + 1) F u = opT a n F u -
      (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F u := by sorry
