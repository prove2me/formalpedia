-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contactSet_eq_singleton_of_exposed_of_local_bounds_readable
-- name    : FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:51.753621+00:00
-- url     : https://prove2.me/theorems/b68b47d0-6adf-4db3-9250-a72ca18aaa5f
-- title:
--   Localized Exposed Contact Set Is Singleton
-- statement:
--   This is the localized Caffarelli contact-set lemma.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. For $x_0,p\in E$, assume the affine function $u(x_0)+\langle p,x-x_0\rangle$ supports $u$ from below:
--   $$u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y\in E.$$
--   Let
--   $$C=\{x:u(x)=u(x_0)+\langle p,x-x_0\rangle\}.$$
--   Assume:
--
--   1. $C$ is compact.
--   2. $z\in C$ and $\|\theta\|=1$.
--   3. Every other contact point is strictly exposed from $z$ in direction $\theta$: if $x\in C$ and $x\ne z$, then $\langle x-z,\theta\rangle<0$.
--   4. $h>0$.
--   5. There is an open set $U$ containing the slab piece $C\cap\{x:-h\le\langle x-z,\theta\rangle\}$.
--   6. For every compact $Q\subseteq U$, there are real numbers $a,b$ with $a>0$ such that every open $G$ with $\overline G\subseteq Q$ satisfies
--      $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G),$$
--      where the measures are `ENNReal` values and `subgradientImage` is written as $\partial u(G)$.
--
--   Then
--   $$C=\{z\}.$$
--
--   This is a localized technical form of the exposed-contact argument and is reusable when Alexandrov bounds are available only on compact subsets of an open region.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contactSet_eq_singleton_of_exposed_of_local_bounds {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
--       (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫})
--       {z θ : E} (hz : u z = u x₀ + ⟪p, z - x₀⟫) (hθ : ‖θ‖ = 1)
--       (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ z → ⟪x - z, θ⟫ < 0) {h : ℝ} (hh : 0 < h)
--       {U : Set E} (hU : IsOpen U)
--       (hCU : {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U)
--       (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ U → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G →
--         closure G ⊆ Q →
--         ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
--         (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
--       {x | u x = u x₀ + ⟪p, x - x₀⟫} = {z}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Selected supporting theorems: [`exists_affine_normalization`](https://prove2.me/theorems/eaae9cde-a1a3-4aa1-8fc7-b6ed5d522bb4), [`exists_compact_sections_subset_and_shrink`](https://prove2.me/theorems/e7f0ab2e-a85f-430a-8fd7-c28dea0e4a20), [`exists_pos_alexandrov_maximum_principle`](https://prove2.me/theorems/fb6f8a3c-985d-4638-9d88-5993fe585328), [`infDist_frontier_image_le_of_width`](https://prove2.me/theorems/942275ce-7a7e-445b-9191-6b35e86c5433), [`volume_subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/17cd1bb9-8c78-49af-a2a8-52c8ebcc13dc).
--
--   Previous: [`contact_stepA`](https://prove2.me/theorems/8b79d3f8-eb05-43a8-ba70-26607440bbcb) · Next: [`strictConvexOn_of_contact_eq`](https://prove2.me/theorems/6e139777-147e-446b-9423-99da9a6d9b75).
--
--   [Source excerpt, lines 675–685](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L675-L685) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L670-L1011 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 4000000

theorem FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_readable {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫})
    {z θ : E} (hz : u z = u x₀ + ⟪p, z - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ z → ⟪x - z, θ⟫ < 0) {h : ℝ} (hh : 0 < h)
    {U : Set E} (hU : IsOpen U)
    (hCU : {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U)
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ U → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G →
      closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    {x | u x = u x₀ + ⟪p, x - x₀⟫} = {z} := by sorry
