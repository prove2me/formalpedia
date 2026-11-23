-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_zero_right
-- name    : GroundTheory.Automorphic.LineKernel.coef_zero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:57.877399+00:00
-- url     : https://prove2.me/theorems/c6092435-cd8d-4543-8660-c53392ef82ca
-- title:
--   Line Kernel: coef zero right
-- statement:
--   The Line Kernel construction uses the coef zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L114-L117

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

theorem GroundTheory.Automorphic.LineKernel.coef_zero_right (a : ℕ → ℝ) (n : ℕ) : coef a n 0 = 1 := by sorry
