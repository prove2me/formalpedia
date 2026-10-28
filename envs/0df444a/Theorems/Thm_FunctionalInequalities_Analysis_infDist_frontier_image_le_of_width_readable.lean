-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_image_le_of_width_readable
-- name    : FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:51.083491+00:00
-- url     : https://prove2.me/theorems/942275ce-7a7e-445b-9191-6b35e86c5433
-- title:
--   Affine Image Frontier Bound from Widths
-- statement:
--   This formalizes the affine-normalized frontier-distance estimate used in the Caffarelli argument.
--
--   Let $E$ be finite-dimensional, let $S\subseteq E$ be open and bounded, let $x\in S$, and let $\theta$ be a unit vector. Suppose $\alpha\ge0$, $\beta>0$, and
--
--   $$
--   \langle y-x,\theta\rangle\le\alpha\quad(y\in S),
--   $$
--
--   while some $y\in S$ satisfies $\langle y-x,\theta\rangle\le-\beta$. If $e:E\simeq_A E$ is an affine equivalence with $e(S)\subseteq\overline B(0,C_0)$ for $C_0>0$, then
--
--   $$
--   \operatorname{infDist}(e(x),\partial(e(S)))\le\frac{2C_0\alpha}{\beta}.
--   $$
--
--   The declaration is `infDist_frontier_image_le_of_width_readable`. The inequalities are respectively non-strict above and strict in the positivity hypothesis for $\beta$ and $C_0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem infDist_frontier_image_le_of_width {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsOpen S)
--       (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {α β : ℝ}
--       (hα : 0 ≤ α) (hβ : 0 < β) (hup : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ α) (hlow : ∃ y ∈ S, ⟪y - x, θ⟫ ≤ -β)
--       (e : E ≃ᵃ[ℝ] E) {C₀ : ℝ} (hC₀ : 0 < C₀) (himg : e '' S ⊆ closedBall (0 : E) C₀) :
--       infDist (e x) (frontier (e '' S)) ≤ 2 * C₀ * α / β
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`infDist_frontier_le_of_forall_inner_le`](https://prove2.me/theorems/bd9c0578-bb14-4e91-95ff-70001c4a6fce).
--
--   Next: [`exists_compact_sections_subset_and_shrink`](https://prove2.me/theorems/e7f0ab2e-a85f-430a-8fd7-c28dea0e4a20).
--
--   [Source excerpt, lines 29–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L29-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L25-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hup : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ α) (hlow : ∃ y ∈ S, ⟪y - x, θ⟫ ≤ -β)
    (e : E ≃ᵃ[ℝ] E) {C₀ : ℝ} (hC₀ : 0 < C₀) (himg : e '' S ⊆ closedBall (0 : E) C₀) :
    infDist (e x) (frontier (e '' S)) ≤ 2 * C₀ * α / β := by sorry
