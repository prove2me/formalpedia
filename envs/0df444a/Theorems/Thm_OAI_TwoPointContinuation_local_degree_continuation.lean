-- Prove2me | Theorems.Thm_OAI_TwoPointContinuation_local_degree_continuation
-- name    : OAI.TwoPointContinuation.local_degree_continuation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:17:44.282762+00:00
-- url     : https://prove2.me/theorems/a757e3fb-0709-4fc5-8d70-558edac3bee5
-- title:
--   OAI.TwoPointContinuation.local_degree_continuation: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwoPointContinuation.local_degree_continuation` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/CompactContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/CompactContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwoPointContinuation`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped Topology`, `open Set Filter Function`):
--
--   ```lean
--    theorem local_degree_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--       (T : ℝ × E → E) (V : Set E) (hV : IsOpen V)
--       (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, ContinuousAt T (t,x))
--       (hzero : ∀ x∈V, T (0,x)=0)
--       (K : Set E) (hK : IsCompact K) (hKV : K⊆V) (h0 : 0∈K)
--       (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, T (t,x)=x → x∈K)
--       (hloc : ∀ t∈Icc (0:ℝ) 1, ∀ x∈K, LocallyPrecompact T (t,x)) :
--       ∃ x∈V, T (1,x)=x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TwoPointContinuation.LocallyPrecompact` (definitions bundle `OAIQ10Bp001` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/CompactContinuation.lean (declaration OAI.TwoPointContinuation.local_degree_continuation)

import Mathlib
import Definitions.Def_OAIQ10Bp001

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
open Set Filter Function
namespace TwoPointContinuation

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

open scoped Topology
open Set Filter Function

 theorem local_degree_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (V : Set E) (hV : IsOpen V)
    (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, ContinuousAt T (t,x))
    (hzero : ∀ x∈V, T (0,x)=0)
    (K : Set E) (hK : IsCompact K) (hKV : K⊆V) (h0 : 0∈K)
    (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, T (t,x)=x → x∈K)
    (hloc : ∀ t∈Icc (0:ℝ) 1, ∀ x∈K, LocallyPrecompact T (t,x)) :
    ∃ x∈V, T (1,x)=x := by
  sorry

end TwoPointContinuation

end

end OAI
end
