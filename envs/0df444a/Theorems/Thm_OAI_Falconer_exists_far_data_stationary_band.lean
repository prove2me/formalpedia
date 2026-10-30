-- Prove2me | Theorems.Thm_OAI_Falconer_exists_far_data_stationary_band
-- name    : OAI.Falconer.exists_far_data_stationary_band
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:15.538187+00:00
-- url     : https://prove2.me/theorems/05bfbcf6-851a-4b3e-a338-75485e3b2b6d
-- title:
--   OAI.Falconer.exists_far_data_stationary_band: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_far_data_stationary_band` of [lean/OAI/MeasureTheory/Falconer/Estimates/FarKernelDataEstimates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/FarKernelDataEstimates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped ENNReal ContDiff`, `open PlanarFalconer (PolicyDescriptor)`):
--
--   ```lean
--    theorem exists_far_data_stationary_band (m K L M : ℕ) (hML : 2*M ≤ L)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
--       (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
--       ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
--         ∀ (D : JetStateFarData m B') (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
--           (w₀ : Sphere (m+3)) (b : ℕ), b ∈ Finset.Icc (D.a+9) (D.h+6) →
--         ENNReal.ofReal D.prefactor *
--           (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
--             ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
--           D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.JetStateFarData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.JetStateFarData.collisionTerm`, `OAI.Falconer.JetStateFarData.originalMeasure`, `OAI.Falconer.JetStateFarData.prefactor` and `OAI.Falconer.JetStateFarData.stationaryKernel` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.comparableFarRegion` and `OAI.Falconer.comparableLengthBand` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_far_data_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/FarKernelDataEstimates.lean (declaration OAI.Falconer.exists_far_data_stationary_band)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_far_data_stationary_band (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B') (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
        (w₀ : Sphere (m+3)) (b : ℕ), b ∈ Finset.Icc (D.a+9) (D.h+6) →
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
          ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
        D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b := by
  sorry

end Falconer

end OAI
end
