-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_contDiff_complexLaplaceBeltrami_self
-- name    : OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:22:57.862628+00:00
-- url     : https://prove2.me/theorems/458d0506-618d-47d9-b744-a1c38a999166
-- title:
--   OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self` of [lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped ContDiff Topology`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter Matrix Manifold`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma contDiff_complexLaplaceBeltrami_self (g : SmoothMetric E E) {u : E → ℂ}
--       (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (complexLaplaceBeltrami g u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.complexLaplaceBeltrami` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_exists_metric_sign_quasimodes_subregions_supported` and `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/BilinearCoordinateMatrixPosDef.lean (declaration OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma contDiff_complexLaplaceBeltrami_self (g : SmoothMetric E E) {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (complexLaplaceBeltrami g u) := by
  sorry

end

open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end
