-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_cutoff_exactification_in_smooth_neighborhood
-- name    : OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:37:10.743616+00:00
-- url     : https://prove2.me/theorems/e8148654-c01a-44a0-bf0e-54a801c53f99
-- title:
--   OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood` of [lean/OAI/Geometry/SmoothYau/Smoothness/CutoffExactificationSmoothNeighborhood.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/CutoffExactificationSmoothNeighborhood.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle MeasureTheory NNReal`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Topology NNReal`, `open Set Filter Module`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter`, `open scoped Topology`, `open Set Filter Function MeasureTheory FourierTransform TemperedDistribution`, `open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Manifold Bundle Matrix`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`):
--
--   ```lean
--   theorem cutoff_exactification_in_smooth_neighborhood
--       (hdim : Module.finrank ℝ E=3) (g : SmoothMetric E M)
--       (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N)
--       (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
--       ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
--       ∀ (b s U v : M → ℝ) (Λ : ℝ) (O F : Set M),
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
--         1 ≤ Λ → (∀ x, 0 < b x) → (∀ x, χ x ∈ Icc (0:ℝ) 1) →
--         (∀ x, |v x-1| ≤ 1/2) → (∀ x, |s x-1| ≤ 1/2) →
--         (∀ x, weightedLaplacian g b U x+Λ*s x*U x=0) →
--         (∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x) →
--         IsOpen O → IsOpen F → (∀ x ∈ O, χ x=1) → (∀ x ∈ F, χ x=0) →
--         (∀ x ∈ F, b x=1 ∧ s x=1) →
--         (∀ x, |Λ⁻¹*cutoffFactor χ v x*weightedLaplacian g b (cutoffFactor χ v) x| ≤ 1/16) →
--         (∀ x ∉ O ∪ F,
--           U x^2*coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x <
--             cutoffFactor χ v x^2*coordinateGradientPair g U U x) →
--         ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
--         (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
--           ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
--         (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
--           ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
--         (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
--           ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
--         (∀ t ∈ tests, ∀ x ∈ t.compactSet, (chartAt E t.center).symm x ∉ O ∪ F →
--           ∀ i j : CoordIndex E, ∀ k ≤ h,
--             ‖iteratedFDeriv ℝ k (chartGradientProjection g (fun z => U z/cutoffFactor χ v z) t.center i j) x‖ ≤ C*n^k) →
--         ∃ ĝ ∈ N, ∃ u : M → ℝ,
--           ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
--           (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
--           (∀ x, u x=U x/cutoffFactor χ v x) ∧
--           (∀ x, u x=0 ↔ U x=0) ∧ (∀ x, 0 < u x ↔ 0 < U x) ∧
--           (∀ x ∈ F, (∀ a c, ĝ.inner x a c=g.inner x a c) ∧ u x=U x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.cutoffFactor` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.chartGradientProjection` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_spherical_exact_stage` and `OAI.YauCounterexamples.exists_three_exact_stage` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/CutoffExactificationSmoothNeighborhood.lean (declaration OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem cutoff_exactification_in_smooth_neighborhood
    (hdim : Module.finrank ℝ E=3) (g : SmoothMetric E M)
    (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (b s U v : M → ℝ) (Λ : ℝ) (O F : Set M),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      1 ≤ Λ → (∀ x, 0 < b x) → (∀ x, χ x ∈ Icc (0:ℝ) 1) →
      (∀ x, |v x-1| ≤ 1/2) → (∀ x, |s x-1| ≤ 1/2) →
      (∀ x, weightedLaplacian g b U x+Λ*s x*U x=0) →
      (∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x) →
      IsOpen O → IsOpen F → (∀ x ∈ O, χ x=1) → (∀ x ∈ F, χ x=0) →
      (∀ x ∈ F, b x=1 ∧ s x=1) →
      (∀ x, |Λ⁻¹*cutoffFactor χ v x*weightedLaplacian g b (cutoffFactor χ v) x| ≤ 1/16) →
      (∀ x ∉ O ∪ F,
        U x^2*coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x <
          cutoffFactor χ v x^2*coordinateGradientPair g U U x) →
      ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, (chartAt E t.center).symm x ∉ O ∪ F →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g (fun z => U z/cutoffFactor χ v z) t.center i j) x‖ ≤ C*n^k) →
      ∃ ĝ ∈ N, ∃ u : M → ℝ,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
        (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
        (∀ x, u x=U x/cutoffFactor χ v x) ∧
        (∀ x, u x=0 ↔ U x=0) ∧ (∀ x, 0 < u x ↔ 0 < U x) ∧
        (∀ x ∈ F, (∀ a c, ĝ.inner x a c=g.inner x a c) ∧ u x=U x) := by
  sorry

end YauCounterexamples
end

end OAI
end
