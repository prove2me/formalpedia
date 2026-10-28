-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_finite_field_scalarization
-- name    : OAI.ScalarConductivity.finite_field_scalarization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:01:48.86132+00:00
-- url     : https://prove2.me/theorems/57648feb-25a8-4211-97f8-49cc1a2f28b2
-- title:
--   OAI.ScalarConductivity.finite_field_scalarization: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.finite_field_scalarization` of [lean/OAI/Analysis/Conductivity/Scalarization/UniformMatrixScalarization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/UniformMatrixScalarization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open MeasureTheory Set Filter Topology TopologicalSpace Matrix`, `open scoped ENNReal Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem finite_field_scalarization
--       (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
--       {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
--       {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
--       [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
--       [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
--       (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
--       (hu : MemLp u 2 (μ.restrict U))
--       (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
--       (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
--       (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
--       (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
--       (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
--         tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
--       (hreg : μ (U \ regularRegion u A U) = 0)
--       (hbound : ∀ᵐ x ∂μ, x ∈ U → ∀ v : Coord3,
--         c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A x).val *ᵥ v) ∧
--         v ⬝ᵥ ((A x).val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
--       ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
--         Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
--         z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
--         (∀ᵐ x ∂μ.restrict U, s x ∈ Icc (laminateLower c C) (laminateUpper C) ∧
--           F x = s x • (z.val.2 x)) ∧
--         (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
--         (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.Symmetric3` and `OAI.ScalarConductivity.regularRegion` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.FieldVector` and `OAI.ScalarConductivity.laminateUpper` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.laminateLower` (definitions bundle `OAIQ059C002` of this split); `OAI.ScalarConductivity.conductivityFlux`, `OAI.ScalarConductivity.instMeasurableSpaceSymmetric3`, `OAI.ScalarConductivity.voltageFlux` and `OAI.ScalarConductivity.voltageGradient` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.SmoothFluxIntegrable` and `OAI.ScalarConductivity.VoltageJetSpace` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.voltageH1Jets` (definitions bundle `OAIQ059C007` of this split); `OAI.ScalarConductivity.zeroVoltageJets` (definitions bundle `OAIQ059C008` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/UniformMatrixScalarization.lean (declaration OAI.ScalarConductivity.finite_field_scalarization)

import Mathlib
import Definitions.Def_OAIQ059C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

theorem finite_field_scalarization
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hu : MemLp u 2 (μ.restrict U))
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hbound : ∀ᵐ x ∂μ, x ∈ U → ∀ v : Coord3,
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A x).val *ᵥ v) ∧
      v ⬝ᵥ ((A x).val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
    ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc (laminateLower c C) (laminateUpper C) ∧
        F x = s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0) := by
  sorry

end ScalarConductivity

end
end

end OAI
end
