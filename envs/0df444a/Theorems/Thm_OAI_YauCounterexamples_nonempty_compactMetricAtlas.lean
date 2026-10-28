-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas
-- name    : OAI.YauCounterexamples.nonempty_compactMetricAtlas
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:26:01.540022+00:00
-- url     : https://prove2.me/theorems/72b6b061-3f82-497e-b0e6-902a6e4d2a12
-- title:
--   OAI.YauCounterexamples.nonempty_compactMetricAtlas: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.nonempty_compactMetricAtlas` of [lean/OAI/Geometry/SmoothYau/Smoothness/ChartDerivativeNeZeroTransfer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ChartDerivativeNeZeroTransfer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open scoped Manifold BoundedContinuousFunction`):
--
--   ```lean
--   theorem nonempty_compactMetricAtlas (g : SmoothMetric E M) (k : ℕ)
--       (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) :
--       Nonempty (CompactMetricAtlas g k hs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor`, `OAI_YauCounterexamples_CompactMetricAtlas_represented_weighted_quintic_smooth`, `OAI_YauCounterexamples_CompactMetricAtlas_shiftedInverse_eigenfunction`, `OAI.YauCounterexamples.exists_annular_simple_pinned_family`, `OAI.YauCounterexamples.exists_spherical_exact_stage`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.exists_three_exact_stage`, `OAI.YauCounterexamples.exists_three_fixed_witnesses`, `OAI.YauCounterexamples.exists_three_scalar_producer`, `OAI.YauCounterexamples.exists_three_simple_pinned_family`, `OAI.YauCounterexamples.spherical_largeWitness_eventually`, `OAI_YauCounterexamples_spherical_simple_eigenpair_open` and `OAI_YauCounterexamples_three_largeWitness_eventually` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ChartDerivativeNeZeroTransfer.lean (declaration OAI.YauCounterexamples.nonempty_compactMetricAtlas)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem nonempty_compactMetricAtlas (g : SmoothMetric E M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) :
    Nonempty (CompactMetricAtlas g k hs) := by
  sorry

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end
