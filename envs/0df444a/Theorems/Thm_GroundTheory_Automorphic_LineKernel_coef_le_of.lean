-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_le_of
-- name    : GroundTheory.Automorphic.LineKernel.coef_le_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:18.404193+00:00
-- url     : https://prove2.me/theorems/0a874e08-286e-453c-a3a3-8fa5c79353c2
-- title:
--   Line Kernel: coef le of
-- statement:
--   The Line Kernel construction uses the coef le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L198-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L198-L236

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

theorem GroundTheory.Automorphic.LineKernel.coef_le_of {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : coef a n p ≤ β p := by sorry
