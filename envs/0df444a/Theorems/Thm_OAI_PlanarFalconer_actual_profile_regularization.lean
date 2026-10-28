-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_actual_profile_regularization
-- name    : OAI.PlanarFalconer.actual_profile_regularization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:55:23.681604+00:00
-- url     : https://prove2.me/theorems/e88dd5ab-5c6b-483f-aa4e-6d42950b3a2f
-- title:
--   OAI.PlanarFalconer.actual_profile_regularization: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.actual_profile_regularization` of [lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualRegularizedClasses.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualRegularizedClasses.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set Metric MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem actual_profile_regularization (Q : DyadicSquare) (hQ : 0 < Q.side)
--       (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
--       {δ C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
--       (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
--       ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
--         let B := N/H
--         let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
--         let L := regularizationLeaves Q μ N
--         let F := regularizationLabel Q μ N B
--         (retainedClassLabels Q μ N B t).card ≤ (4*N+1)^(2*H+1) ∧
--         μ (retainedClassUnion Q μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
--           (((4*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
--         ∀ T ∈ retainedClassLabels Q μ N B t,
--           t ≤ classMeasure Q μ L F T univ ∧
--           ∃ m : ℝ → ℝ, RegularizedProfileData Q (normalizedClass Q μ L F T) N B δ lam m
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.classMeasure`, `OAI.PlanarFalconer.normalizedClass`, `OAI.PlanarFalconer.regularizationLabel`, `OAI.PlanarFalconer.regularizationLeaves`, `OAI.PlanarFalconer.retainedClassLabels`, `OAI.PlanarFalconer.retainedClassUnion` and `OAI.PlanarFalconer.DyadicSquare.carrier` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.two_root_has_shell_approximations` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Estimates/ActualRegularizedClasses.lean (declaration OAI.PlanarFalconer.actual_profile_regularization)

import Mathlib
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

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

theorem actual_profile_regularization (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (retainedClassLabels Q μ N B t).card ≤ (4*N+1)^(2*H+1) ∧
      μ (retainedClassUnion Q μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        (((4*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ m : ℝ → ℝ, RegularizedProfileData Q (normalizedClass Q μ L F T) N B δ lam m := by
  sorry

end PlanarFalconer

end OAI
end
