-- Prove2me | Theorems.Thm_OAI_Falconer_finite_euclidean_radial_testNorm_moment
-- name    : OAI.Falconer.finite_euclidean_radial_testNorm_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:51:15.85087+00:00
-- url     : https://prove2.me/theorems/a0fa897a-3041-4fce-9240-cc3c365d118d
-- title:
--   OAI.Falconer.finite_euclidean_radial_testNorm_moment: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.finite_euclidean_radial_testNorm_moment` of [lean/OAI/MeasureTheory/Falconer/Radial/RadialTestMoment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/RadialTestMoment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory Filter PlanarFalconer`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem finite_euclidean_radial_testNorm_moment (n : ℕ)
--       (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
--       {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
--       (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
--       (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
--       (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
--       (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
--       (hEα : rieszEnergyOn α s < ∞) (hEβ : rieszEnergyOn β t < ∞) :
--       (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) < ∞
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.rieszEnergyOn` (definitions bundle `OAIQ038F001` of this split); `OAI.Falconer.Space` and `OAI.Falconer.radialDirection` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.surfaceTestNorm` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.falconer_distance_conjecture` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/RadialTestMoment.lean (declaration OAI.Falconer.finite_euclidean_radial_testNorm_moment)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology

theorem finite_euclidean_radial_testNorm_moment (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
    (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
    (hEα : rieszEnergyOn α s < ∞) (hEβ : rieszEnergyOn β t < ∞) :
    (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) < ∞ := by
  sorry

end Falconer

end OAI
end
