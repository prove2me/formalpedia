-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable
-- name    : FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:14.294593+00:00
-- url     : https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e
-- title:
--   Subgradient Realizing the One-Sided Convex Slope
-- statement:
--   This is an auxiliary max-formula statement for directional slopes of finite convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex on all of $E$. For every $x,v\in E$, there exists $g\in E$ such that:
--
--   1. $g$ is a subgradient of $u$ at $x$:
--      $$u(x)+\langle g,y-x\rangle\le u(y)\qquad\text{for every }y\in E.$$
--   2. For every $\varepsilon>0$, there exists $t>0$ with
--      $$\frac{u(x+t v)-u(x)}{t}\le \langle g,v\rangle+\varepsilon.$$
--
--   Thus the pairing with $v$ is approximated from above by positive directional difference quotients, while the subgradient inequality supplies the corresponding lower bound. The declaration `exists_subgradient_slope_le_inner_add_readable` is useful for selecting subgradients compatible with one-sided directional derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_subgradient_slope_le_inner_add {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
--       (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
--       ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
--         ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`subgradient_mem_of_ae_gradient_mem`](https://prove2.me/theorems/6f655218-b30e-46bf-be4f-c590531dd524) · Next: [`ConvexOn.ae_differentiableAt_of_isOpen`](https://prove2.me/theorems/b601dd62-f116-4daf-a684-024dc3b2b841).
--
--   [Source excerpt, lines 208–212](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L208-L212) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L202-L553 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
    ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
      ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε := by sorry
