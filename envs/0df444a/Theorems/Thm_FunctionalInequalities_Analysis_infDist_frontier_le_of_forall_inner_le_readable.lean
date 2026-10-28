-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_le_of_forall_inner_le_readable
-- name    : FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:55.238754+00:00
-- url     : https://prove2.me/theorems/bd9c0578-bb14-4e91-95ff-70001c4a6fce
-- title:
--   Frontier Distance Bounded by Directional Width
-- statement:
--   This proves that the distance to the frontier is bounded by a one-sided width.
--
--   Let $E$ be a normed real inner-product space, let $S\subseteq E$ be open and bounded, let $x\in S$, and let $\theta$ be a unit vector. If for some $t\in\mathbb R$,
--
--   $$
--   \langle y-x,\theta\rangle\le t\qquad\text{for every }y\in S,
--   $$
--
--   then
--
--   $$
--   \operatorname{infDist}(x,\partial S)\le t.
--   $$
--
--   The declaration is `infDist_frontier_le_of_forall_inner_le_readable`. No finite-dimensionality or convexity assumption appears in the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem infDist_frontier_le_of_forall_inner_le {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
--       {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
--       infDist x (frontier S) ≤ t
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`volume_subgradientImage_quadraticAt_aux`](https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231) · Next: [`subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/3ad116ee-9145-4587-a1b0-81a8f51d65df).
--
--   [Source excerpt, lines 1687–1690](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1687-L1690) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1685-L1740 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open Set Metric
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
    infDist x (frontier S) ≤ t := by sorry
