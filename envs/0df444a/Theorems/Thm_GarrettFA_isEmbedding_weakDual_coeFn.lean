-- Prove2me | Theorems.Thm_GarrettFA_isEmbedding_weakDual_coeFn
-- name    : GarrettFA.isEmbedding_weakDual_coeFn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:40:27.363222+00:00
-- url     : https://prove2.me/theorems/c0d7af89-b193-4dea-915d-7a78424d1f82
-- title:
--   Claim 5.0.6 — the weak dual embeds in the limit of the finite-dimensional spaces $V^*_\Phi$
-- statement:
--   Let $V$ be a Hausdorff locally convex topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$. The map sending a continuous linear functional $\lambda$ to its values $(\lambda(v))_{v\in V}$,
--
--   $$V^*_\sigma \longrightarrow \mathbb K^V,$$
--
--   is a topological embedding, and its image consists of linear functionals.
--
--   **Formalization Note** In the notes, $V^*$ injects continuously into the projective limit $\lim_\Phi V^*_\Phi$ over finite subsets $\Phi\subset V$, where $V^*_\Phi$ is the (finite-dimensional) Hausdorff completion of $V^*$ for the seminorm $p_\Phi(\lambda)=\sum_{v\in\Phi}|\lambda(v)|$, and the weak topology is the subspace topology. $V^*_\Phi$ is identified with the image of $V^*$ in $\mathbb K^\Phi$, so the projective limit is a subspace of $\mathbb K^V=\lim_\Phi\mathbb K^\Phi$, contained in the linear functionals. The formal statement is the embedding into $\mathbb K^V$ with image among the linear functionals.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, pp. 8–9, Claim 5.0.6

import Mathlib

namespace GarrettFA
theorem isEmbedding_weakDual_coeFn {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    [LocallyConvexSpace ℝ V] :
    Topology.IsEmbedding (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) ∧
      Set.range (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) ⊆ {g : V → 𝕜 | IsLinearMap 𝕜 g} := by sorry
end GarrettFA
