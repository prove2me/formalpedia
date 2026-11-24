-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzDiv_contDiff_integral_smul_param
-- name    : GlobalTheory.SchwartzDiv.contDiff_integral_smul_param
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:37.496996+00:00
-- url     : https://prove2.me/theorems/c3f3fbe0-3ef1-4f7e-a8c0-fd3091dfc0a7
-- title:
--   Schwartz Div: cont Diff integral smul param
-- statement:
--   The Schwartz Div construction uses the cont Diff integral smul param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L44-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv
variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem GlobalTheory.SchwartzDiv.contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by sorry
