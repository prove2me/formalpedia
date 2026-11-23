-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wSpan_deriv
-- name    : GlobalTheory.HeckeTwo.HDecay.wSpan_deriv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:43.844875+00:00
-- url     : https://prove2.me/theorems/30583444-bb9a-4537-863b-4e3d68e3ae3d
-- title:
--   HDecay: w Span deriv
-- statement:
--   The HDecay construction uses the w Span deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L155-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L155-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {σ y}

theorem GlobalTheory.HeckeTwo.HDecay.wSpan_deriv (hy : y ≠ 0) {F : ℝ → ℂ} (hF : F ∈ wSpan σ y) :
    Differentiable ℝ F ∧ deriv F ∈ wSpan σ y := by sorry
