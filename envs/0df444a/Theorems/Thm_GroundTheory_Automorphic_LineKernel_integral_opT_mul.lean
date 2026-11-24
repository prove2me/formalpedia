-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_opT_mul
-- name    : GroundTheory.Automorphic.LineKernel.integral_opT_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:34.908206+00:00
-- url     : https://prove2.me/theorems/4fac0842-8b53-40ca-a2c9-15386b568c19
-- title:
--   Line Kernel: integral op T mul
-- statement:
--   The Line Kernel construction uses the integral op T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L176-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L176-L197

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

theorem GroundTheory.Automorphic.LineKernel.integral_opT_mul (a : ℕ → ℝ) (n : ℕ) {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ u, opT a n F u * ψ u =
      ∫ u, F u * ∑ p ∈ Finset.range (n + 1), (coef a n p : ℂ) * iteratedDeriv p ψ u := by sorry
