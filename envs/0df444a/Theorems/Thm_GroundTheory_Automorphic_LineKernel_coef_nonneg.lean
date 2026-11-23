-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_nonneg
-- name    : GroundTheory.Automorphic.LineKernel.coef_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:41.557981+00:00
-- url     : https://prove2.me/theorems/8e3adb5f-3c4f-4c82-9c5b-235fd9dfbba2
-- title:
--   Line Kernel: coef nonneg
-- statement:
--   The Line Kernel construction uses the coef nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L128-L134

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

theorem GroundTheory.Automorphic.LineKernel.coef_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : 0 ≤ coef a n p := by sorry
