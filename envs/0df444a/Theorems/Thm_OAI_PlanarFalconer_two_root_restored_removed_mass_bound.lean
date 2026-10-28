-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_two_root_restored_removed_mass_bound
-- name    : OAI.PlanarFalconer.two_root_restored_removed_mass_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:00:49.277374+00:00
-- url     : https://prove2.me/theorems/9779353c-4aaf-4701-b62f-65133ceee865
-- title:
--   OAI.PlanarFalconer.two_root_restored_removed_mass_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.two_root_restored_removed_mass_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootRestoration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootRestoration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set Metric MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem two_root_restored_removed_mass_bound (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
--       (μ ν : ProbabilityMeasure Plane) (m₁ m₂ : List ℕ → ℝ → ℝ)
--       {N H₁ H₂ : ℕ} (hN : 0 < N) (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (β : ℝ)
--       (hf₁ : ActualClassFamily Q₀ μ N H₁ δ lam sig m₁) (hf₂ : ActualClassFamily Q₁ ν N H₂ δ lam sig m₂)
--       {p q : ℝ} (hpq : p.HolderConjugate q) {K C : ENNReal} (hK : K ≠ ∞)
--       (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
--       (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
--       (hweight : ∀ᵐ z ∂(μ:Measure Plane).prod ν, distanceWeight z ≤ C) :
--       restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β univ ≤
--         C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
--           K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.ActualClassFamily`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.UnitCircle` and `OAI.PlanarFalconer.sourceRadialUnit` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.distanceWeight`, `OAI.PlanarFalconer.restorationArcBound` and `OAI.PlanarFalconer.restorationDiscardBound` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.restoredTwoRootRemoved` and `OAI.PlanarFalconer.sourceDensityNorm` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.two_root_has_shell_approximations` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/TwoRootRestoration.lean (declaration OAI.PlanarFalconer.two_root_restored_removed_mass_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem two_root_restored_removed_mass_bound (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : ProbabilityMeasure Plane) (m₁ m₂ : List ℕ → ℝ → ℝ)
    {N H₁ H₂ : ℕ} (hN : 0 < N) (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (β : ℝ)
    (hf₁ : ActualClassFamily Q₀ μ N H₁ δ lam sig m₁) (hf₂ : ActualClassFamily Q₁ ν N H₂ δ lam sig m₂)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K C : ENNReal} (hK : K ≠ ∞)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    (hweight : ∀ᵐ z ∂(μ:Measure Plane).prod ν, distanceWeight z ≤ C) :
    restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β univ ≤
      C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p)) := by
  sorry

end PlanarFalconer

end OAI
end
