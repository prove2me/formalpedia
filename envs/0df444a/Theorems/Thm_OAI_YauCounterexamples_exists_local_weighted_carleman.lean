-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_local_weighted_carleman
-- name    : OAI.YauCounterexamples.exists_local_weighted_carleman
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:04:23.38039+00:00
-- url     : https://prove2.me/theorems/ab297072-4329-4b45-ad7f-37a08ba25356
-- title:
--   OAI.YauCounterexamples.exists_local_weighted_carleman: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_local_weighted_carleman` of [lean/OAI/Geometry/SmoothYau/Estimates/TestPairSubSquareBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/TestPairSubSquareBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open MeasureTheory TopologicalSpace Filter Set`, `open scoped Distributions ContDiff Topology`):
--
--   ```lean
--   theorem exists_local_weighted_carleman (a : ι → ι → SmoothScalar E)
--       (ha : ∀ i j, a i j = a j i) (V ψ : SmoothScalar E) (x₀ : E)
--       (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
--       (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
--       ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
--         ∀ τ ≥ T, ∀ u : EllipticTest K,
--           testPair K (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u)
--             (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u) ≤
--           8 * testPair K
--             (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u))
--             (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.EllipticTest`, `OAI.YauCounterexamples.SmoothScalar` and `OAI.YauCounterexamples.SmoothScalar.directional` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.convexifyPhase`, `OAI.YauCounterexamples.exponentialWeight`, `OAI.YauCounterexamples.testMultiply` and `OAI.YauCounterexamples.testPair` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.testSchrodinger` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.proportional_eigen_global` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/TestPairSubSquareBound.lean (declaration OAI.YauCounterexamples.exists_local_weighted_carleman)

import Mathlib
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

theorem exists_local_weighted_carleman (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V ψ : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0) :
    ∃ H > 0, ∃ U ∈ 𝓝 x₀, ∃ T > 0, ∀ (K : Compacts E), (↑K : Set E) ⊆ U →
      ∀ τ ≥ T, ∀ u : EllipticTest K,
        testPair K (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u)
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) u) ≤
        8 * testPair K
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u))
          (testMultiply K (exponentialWeight (convexifyPhase ψ H) τ) (testSchrodinger K e a V u)) := by
  sorry

end YauCounterexamples
end

end OAI
end
