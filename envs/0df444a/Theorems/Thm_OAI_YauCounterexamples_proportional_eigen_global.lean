-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_proportional_eigen_global
-- name    : OAI.YauCounterexamples.proportional_eigen_global
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:21:06.657401+00:00
-- url     : https://prove2.me/theorems/56a8adf3-f643-4e93-bf6c-6c8905fee839
-- title:
--   OAI.YauCounterexamples.proportional_eigen_global: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.proportional_eigen_global` of [lean/OAI/Geometry/SmoothYau/Spectrum/TransverseZeroKernel.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/TransverseZeroKernel.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma proportional_eigen_global [PreconnectedSpace M] (g : SmoothMetric E M)
--       {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
--       (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (ell c : ℝ)
--       (hue : ∀ x, -laplaceBeltrami g u x = ell*u x)
--       (hve : ∀ x, -laplaceBeltrami g v x = ell*v x)
--       (he : ∃ x, v =ᶠ[𝓝 x] (fun y => c*u y)) : v = fun y => c*u y
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero` and `OAI.YauCounterexamples.three_rank_separating_tensor` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/TransverseZeroKernel.lean (declaration OAI.YauCounterexamples.proportional_eigen_global)

import Mathlib
import Definitions.Def_SmoothYau

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma proportional_eigen_global [PreconnectedSpace M] (g : SmoothMetric E M)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (ell c : ℝ)
    (hue : ∀ x, -laplaceBeltrami g u x = ell*u x)
    (hve : ∀ x, -laplaceBeltrami g v x = ell*v x)
    (he : ∃ x, v =ᶠ[𝓝 x] (fun y => c*u y)) : v = fun y => c*u y := by
  sorry

end YauCounterexamples
end

end OAI
end
