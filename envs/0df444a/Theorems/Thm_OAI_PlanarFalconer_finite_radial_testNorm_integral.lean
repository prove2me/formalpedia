-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_finite_radial_testNorm_integral
-- name    : OAI.PlanarFalconer.finite_radial_testNorm_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:59:50.779583+00:00
-- url     : https://prove2.me/theorems/e641ae96-7843-4c36-b97f-3b49dae1b0d6
-- title:
--   OAI.PlanarFalconer.finite_radial_testNorm_integral: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.finite_radial_testNorm_integral` of [lean/OAI/MeasureTheory/Falconer/Falconer/Radial/FiniteRadialTestEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Radial/FiniteRadialTestEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem finite_radial_testNorm_integral (α β : Measure Plane)
--       [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
--       (hαK : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
--       (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
--       (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
--       (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
--       (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
--       (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x)
--       (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
--       (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) < ∞
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.UnitCircle` and `OAI.PlanarFalconer.sourceRadialUnit` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.rieszEnergy` and `OAI.PlanarFalconer.sourceTestNorm` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.exists_normalized_root_setup` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Radial/FiniteRadialTestEnergy.lean (declaration OAI.PlanarFalconer.finite_radial_testNorm_integral)

import Mathlib
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem finite_radial_testNorm_integral (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hαK : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) < ∞ := by
  sorry

end PlanarFalconer

end OAI
end
