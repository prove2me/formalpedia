-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable
-- name    : FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:42.656168+00:00
-- url     : https://prove2.me/theorems/f79e9028-f752-4900-ae74-36d3b8229978
-- title:
--   Sliding Lemma for the Subgradient Image
-- statement:
--   This formalizes the sliding lemma for the Alexandrov maximum principle.
--
--   Let $E$ be finite-dimensional, let $u:E\to\mathbb R$ be convex, and let $\Omega\subseteq E$ be open and bounded. Assume:
--
--   1. $u\ge0$ on $\partial\Omega$.
--   2. $x_0\in\Omega$ and $u(x_0)<0$.
--   3. For some $p\in E$, the affine function satisfies
--      $$u(x_0)+\langle p,x-x_0\rangle\le0$$
--      for every $x\in\overline\Omega$.
--
--   Then $p$ belongs to the subgradient image of $u$ over $\Omega$:
--
--   $$
--   p\in\operatorname{subgradientImage}(u,\Omega).
--   $$
--
--   The declaration is `mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable`. It asserts membership in the image, not a specified point realizing the subgradient.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mem_subgradientImage_of_affine_le_of_nonneg_frontier {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
--       {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
--       (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
--       {p : E} (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ subgradientImage u Ω
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`lintegral_subgradientImage_eq_of_map_gradient`](https://prove2.me/theorems/72af9bcf-0597-4b8f-9f71-0ba93a4e8609) · Next: [`exists_unit_inner_le_infDist_frontier`](https://prove2.me/theorems/f4f9ef6d-abf7-4073-89c1-856846d679e9).
--
--   [Source excerpt, lines 455–459](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L455-L459) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L450-L605 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open Set Metric
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
    {p : E} (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ subgradientImage u Ω := by sorry
