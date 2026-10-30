-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_normalized_two_ball_obstruction
-- name    : OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:17:12.950842+00:00
-- url     : https://prove2.me/theorems/7ed5fdd5-a49d-4234-b8e3-ab86d5a580a0
-- title:
--   OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology`, `open Set Function Filter`):
--
--   ```lean
--   theorem normalized_two_ball_obstruction (n : ℕ) (hn : 3 ≤ n)
--       (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : HasPacking n 2 1 ![a,b]) : a+b ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.HasPacking` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.packing_necessity` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/PackingNecessity.lean (declaration OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction)

import Mathlib
import Definitions.Def_BallPackingNecessity

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking
section

theorem normalized_two_ball_obstruction (n : ℕ) (hn : 3 ≤ n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : HasPacking n 2 1 ![a,b]) : a+b ≤ 1 := by
  sorry

end

open scoped ENNReal NNReal Topology ContDiff Pointwise
open Set MeasureTheory

open scoped ContDiff Topology
open Set Function

open scoped ContDiff Topology
open Set Function

end HigherDimensionalBallPacking

end

end OAI
end
