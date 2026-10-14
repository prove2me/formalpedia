-- Prove2me | Theorems.Thm_GarrettFA_weakDual_isNetComplete_iff
-- name    : GarrettFA.weakDual_isNetComplete_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:35:16.65414+00:00
-- url     : https://prove2.me/theorems/0dd84af9-9faa-4765-b525-94c6efa33c23
-- title:
--   Thm. 5.0.1 — completeness of weak duals
-- statement:
--   Let $V$ be a Hausdorff locally convex topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$, and let $V^*_\sigma$ be its weak dual: the continuous linear functionals with the topology of pointwise convergence on $V$. Then
--
--   $$V^*_\sigma \text{ is complete} \iff \text{every linear functional } V\to\mathbb K \text{ is continuous}.$$
--
--   Here complete means that every Cauchy net converges.
--
--   **Formalization Note** The weak dual is Mathlib's `WeakDual 𝕜 V`.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Theorem 5.0.1

import Definitions.Def_GarrettFA_IsNetComplete

namespace GarrettFA
theorem weakDual_isNetComplete_iff {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    [LocallyConvexSpace ℝ V] :
    IsNetComplete (WeakDual 𝕜 V) ↔ ∀ f : V →ₗ[𝕜] 𝕜, Continuous f := by sorry
end GarrettFA
