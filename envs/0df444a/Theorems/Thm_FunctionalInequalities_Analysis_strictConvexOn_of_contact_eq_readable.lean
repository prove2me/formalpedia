-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_contact_eq_readable
-- name    : FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:07.704981+00:00
-- url     : https://prove2.me/theorems/6e139777-147e-446b-9423-99da9a6d9b75
-- title:
--   Singleton Supporting Contacts Imply Strict Convexity
-- statement:
--   This states that singleton supporting contact sets imply strict convexity.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Assume that for every $x,p\in E$, whenever
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y,$$
--   any point $y$ satisfying equality must equal $x$:
--   $$u(y)=u(x)+\langle p,y-x\rangle\Longrightarrow y=x.$$
--   Then $u$ is strictly convex on $E$:
--   $$u(a x+b y)<a u(x)+b u(y)$$
--   whenever $x\ne y$, $a,b>0$, and $a+b=1$.
--
--   This is the abstract bridge from uniqueness of supporting contacts to strict convexity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem strictConvexOn_of_contact_eq {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
--       (hcontact : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
--         ∀ y, u y = u x + ⟪p, y - x⟫ → y = x) :
--       StrictConvexOn ℝ univ u
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Previous: [`contactSet_eq_singleton_of_exposed_of_local_bounds`](https://prove2.me/theorems/b68b47d0-6adf-4db3-9250-a72ca18aaa5f) · Next: [`subgradient_mem_interior_of_strictConvexOn`](https://prove2.me/theorems/a618a7d2-7d13-4aef-99ab-5b9c4a71d731).
--
--   [Source excerpt, lines 1110–1113](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1110-L1113) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1107-L1157 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open scoped RealInnerProductSpace
open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_readable {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hcontact : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
      ∀ y, u y = u x + ⟪p, y - x⟫ → y = x) :
    StrictConvexOn ℝ univ u := by sorry
