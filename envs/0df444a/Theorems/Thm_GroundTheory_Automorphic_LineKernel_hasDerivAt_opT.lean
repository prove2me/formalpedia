-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasDerivAt_opT
-- name    : GroundTheory.Automorphic.LineKernel.hasDerivAt_opT
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:10.320825+00:00
-- url     : https://prove2.me/theorems/610c38f2-2035-4790-b70f-76b0d07443f4
-- title:
--   Line Kernel: has Deriv At op T
-- statement:
--   The Line Kernel construction uses the has Deriv At op T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L162-L169

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

theorem GroundTheory.Automorphic.LineKernel.hasDerivAt_opT (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    HasDerivAt (opT a n F)
      (∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F x) x := by sorry
