-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_stage_identity
-- name    : GroundTheory.Automorphic.LineKernel.stage_identity
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:56.112715+00:00
-- url     : https://prove2.me/theorems/eb9b16f4-0c06-4c75-a749-e4168d751ecf
-- title:
--   Line Kernel: stage identity
-- statement:
--   The Line Kernel construction uses the stage identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L283-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L283-L344

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
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem GroundTheory.Automorphic.LineKernel.stage_identity {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    F 0 = (∫ u, opT a (n + 1) F u * KC a r n u) +
      ∑ j ∈ Finset.range (n + 1), ∫ u, F u * ρ a r j u := by sorry
