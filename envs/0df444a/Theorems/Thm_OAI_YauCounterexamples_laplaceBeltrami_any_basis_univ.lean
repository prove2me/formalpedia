-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_laplaceBeltrami_any_basis_univ
-- name    : OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:24:12.692009+00:00
-- url     : https://prove2.me/theorems/3d7588a7-20a4-4e54-a764-c0854f432a6b
-- title:
--   OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ` of [lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle Matrix`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma laplaceBeltrami_any_basis_univ (g : SmoothMetric E M) (p : M)
--       (ht : (chartAt E p).target=univ) (b : Module.Basis ι ℝ E)
--       {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
--       laplaceBeltrami g u p = coordinateMetricLaplacian b
--         (fun y => bilinearCoordinateMatrix b (chartMetricForm g p y))
--         (u ∘ (chartAt E p).symm) (chartAt E p p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.chartMetricForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.bilinearCoordinateMatrix` and `OAI.YauCounterexamples.coordinateMetricLaplacian` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_four_witnesses_unbounded` and `OAI.YauCounterexamples.laplaceBeltrami_four_lift` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean (declaration OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A002
import Definitions.Def_OAIQ070A003

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma laplaceBeltrami_any_basis_univ (g : SmoothMetric E M) (p : M)
    (ht : (chartAt E p).target=univ) (b : Module.Basis ι ℝ E)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
    laplaceBeltrami g u p = coordinateMetricLaplacian b
      (fun y => bilinearCoordinateMatrix b (chartMetricForm g p y))
      (u ∘ (chartAt E p).symm) (chartAt E p p) := by
  sorry

end YauCounterexamples
end

end OAI
end
