-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_continuous_opT
-- name    : GroundTheory.Automorphic.LineKernel.continuous_opT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:44.832974+00:00
-- url     : https://prove2.me/theorems/4e5e0cd6-f4db-479e-96a8-d673b448c128
-- title:
--   Line Kernel: continuous op T
-- statement:
--   The Line Kernel construction uses the continuous op T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L157-L160

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

theorem GroundTheory.Automorphic.LineKernel.continuous_opT (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (opT a n F) := by sorry
