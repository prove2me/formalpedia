-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_unit_inner_le_infDist_frontier_readable
-- name    : FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:00.045464+00:00
-- url     : https://prove2.me/theorems/f4f9ef6d-abf7-4073-89c1-856846d679e9
-- title:
--   Supporting Direction at the Nearest Frontier
-- statement:
--   This formalizes the supporting half-space estimate for a bounded open convex set.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space, let $\Omega\subseteq E$ be open, convex, and bounded, and let $x_0\in\Omega$. Then there exists a unit vector $e\in E$ such that every $x\in\Omega$ satisfies
--
--   $$
--   \langle x-x_0,e\rangle\le\operatorname{infDist}(x_0,\partial\Omega).
--   $$
--
--   The declaration is `exists_unit_inner_le_infDist_frontier_readable`. Here `infDist` is the distance from $x_0$ to the frontier, and the conclusion is existential rather than a uniqueness statement about the supporting direction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_unit_inner_le_infDist_frontier {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
--       (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
--       ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`mem_subgradientImage_of_affine_le_of_nonneg_frontier`](https://prove2.me/theorems/f79e9028-f752-4900-ae74-36d3b8229978) · Next: [`exists_pos_volume_convexHull_closedBall_union_singleton_ge`](https://prove2.me/theorems/04941f10-f990-4b5d-a225-77ccc909d39f).
--
--   [Source excerpt, lines 624–627](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L624-L627) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L620-L731 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open Set Metric
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω) := by sorry
