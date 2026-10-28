-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_interior_of_strictConvexOn_readable
-- name    : FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:09.494543+00:00
-- url     : https://prove2.me/theorems/a618a7d2-7d13-4aef-99ab-5b9c4a71d731
-- title:
--   Strictly Convex Subgradients Lie In Interior
-- statement:
--   This proves interior membership for subgradients of a strictly convex function.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be strictly convex. Let $K\subseteq E$ be convex with nonempty interior. Assume every subgradient of $u$ belongs to $K$:
--   $$\forall x,p,\quad \bigl[\forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\bigr]\Rightarrow p\in K.$$
--   Then every such subgradient lies in the interior:
--   $$\forall x,p,\quad \bigl[\forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\bigr]\Rightarrow p\in\operatorname{int}K.$$
--
--   This strengthens closed-range containment and is used when deriving local density bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradient_mem_interior_of_strictConvexOn {u : E → ℝ}
--       (hstrict : StrictConvexOn ℝ univ u) {K : Set E} (hKc : Convex ℝ K)
--       (hKint : (interior K).Nonempty)
--       (hK : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K)
--       {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ interior K
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Previous: [`strictConvexOn_of_contact_eq`](https://prove2.me/theorems/6e139777-147e-446b-9423-99da9a6d9b75) · Next: [`exists_exposed_contact_of_lt`](https://prove2.me/theorems/955fb26b-d452-446f-81e7-00212e58fa6b).
--
--   [Source excerpt, lines 1162–1166](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1162-L1166) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1159-L1200 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open scoped RealInnerProductSpace
open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_readable {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {K : Set E} (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (hK : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ interior K := by sorry
