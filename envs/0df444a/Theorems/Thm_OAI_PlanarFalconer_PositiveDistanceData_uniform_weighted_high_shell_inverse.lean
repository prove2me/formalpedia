-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_weighted_high_shell_inverse
-- name    : OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:59:17.578982+00:00
-- url     : https://prove2.me/theorems/c1095059-f777-445c-a99a-f2df7034a519
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/WeightedHighShellInverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/WeightedHighShellInverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_weighted_high_shell_inverse {sig T : ℝ} (hsig : 0 < sig) :
--       ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, N₀ ≤ d.N → d.sig = sig →
--       0 < d.Q.side → d.StronglySeparated → 0 < d.q →
--       d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
--       ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
--       ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
--       ‖(d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
--         (((dist x y/(2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
--         sourceInverseCircleIntegral n r (x-y)
--           (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
--           (d.pairMaskSymbol (x,y))‖ ≤ ((2:ℝ)^d.N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.sourceConeCircle`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.descendant`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated`, `OAI.PlanarFalconer.PositiveDistanceData.pairMaskSymbol` and `OAI.PlanarFalconer.PositiveDistanceData.spatialWeight` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.sourceInverseCircleIntegral` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_profile_error` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/WeightedHighShellInverse.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem uniform_weighted_high_shell_inverse {sig T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, N₀ ≤ d.N → d.sig = sig →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
    ‖(d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (((dist x y/(2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
      sourceInverseCircleIntegral n r (x-y)
        (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
        (d.pairMaskSymbol (x,y))‖ ≤ ((2:ℝ)^d.N)^(-T) := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end
