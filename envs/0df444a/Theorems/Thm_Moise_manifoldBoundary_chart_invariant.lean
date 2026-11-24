-- Prove2me | Theorems.Thm_Moise_manifoldBoundary_chart_invariant
-- name    : Moise.manifoldBoundary_chart_invariant
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T21:06:55.379254+00:00
-- url     : https://prove2.me/theorems/47c8e233-eca7-414b-a032-33e55afa38ae
-- title:
--   Chart invariance of the boundary of a topological manifold
-- statement:
--   Let $M$ be a topological $n$-manifold with boundary, and let $x \in \partial M$. Then every half-space coordinate chart $\varphi : U \to V \cap \mathbb{R}^n_+$ around $x$ maps $x$ to the boundary hyperplane $\{y_0 = 0\}$ (so $n > 0$ and $(\varphi(x))_0 = 0$).
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 0.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Moise_Ch0_Ch1_Extra

namespace Moise

theorem manifoldBoundary_chart_invariant (n : ℕ) (M : Type*) [TopologicalSpace M]
    (hM : IsTopologicalManifoldWithBoundary n M) {x : M} (hx : x ∈ manifoldBoundary n M)
    (U : Set M) (V : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hxU : x ∈ U) (hV : IsOpen V)
    (φ : U ≃ₜ {y ∈ V | ∀ h : 0 < n, 0 ≤ y ⟨0, h⟩}) :
    ∃ h : 0 < n, (φ ⟨x, hxU⟩).1 ⟨0, h⟩ = 0 := by sorry

end Moise
