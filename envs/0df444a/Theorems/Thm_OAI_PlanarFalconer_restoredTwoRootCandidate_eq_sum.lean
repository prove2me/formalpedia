-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_restoredTwoRootCandidate_eq_sum
-- name    : OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:38:30.855376+00:00
-- url     : https://prove2.me/theorems/99e1d57c-a29e-47f5-aaa6-d0a3036c9cec
-- title:
--   OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum` of [lean/OAI/MeasureTheory/Falconer/Shells/TwoRootClassMixture.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/TwoRootClassMixture.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem restoredTwoRootCandidate_eq_sum (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
--       [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
--       (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
--       restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β =
--         ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
--           twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
--             twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.restoredTwoRootCandidate`, `OAI.PlanarFalconer.retainedRootPairs`, `OAI.PlanarFalconer.twoRootClassCoefficient` and `OAI.PlanarFalconer.twoRootClassMeasure` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/TwoRootClassMixture.lean (declaration OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem restoredTwoRootCandidate_eq_sum (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β =
      ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
        twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
          twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a := by
  sorry

end PlanarFalconer

end OAI
end
