-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_exists_quadraticAt_expansion_readable
-- name    : FunctionalInequalities.Analysis.ae_exists_quadraticAt_expansion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:28.326348+00:00
-- url     : https://prove2.me/theorems/995efd14-b691-40e5-adc5-c0effdf385d3
-- title:
--   Coordinate Alexandrov Expansion
-- statement:
--   This is the coordinate form of an almost-everywhere second-order expansion.
--
--   Let $n\in\mathbb N$, let $u:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$ be convex on the whole space, and use the coordinate quadratic polynomial `quadraticAt`. For almost every $x$, there exist a real matrix $B$ and a vector $g$ such that:
--
--   1. $B$ is Hermitian, equivalently symmetric over $\mathbb R$.
--   2. For every $\varepsilon>0$, for all $y$ sufficiently near $x$,
--      $$\left|u(y)-\operatorname{quadraticAt}(B,x,g,u(x),y)\right|\le \varepsilon\|y-x\|^2.$$
--
--   The declaration `ae_exists_quadraticAt_expansion_readable` translates the abstract symmetric linear operator in `ae_exists_secondOrder_expansion_readable` into a matrix on `EuclideanSpace ℝ (Fin n)`. It makes no restriction such as $n\ge1$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_exists_quadraticAt_expansion {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ ∃ g : EuclideanSpace ℝ (Fin n),
--           ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Supporting theorems: [`ae_exists_secondOrder_expansion`](https://prove2.me/theorems/5eb08b15-cdd6-4026-aca8-c20821e30f23).
--
--   Previous: [`posDef_and_convolution_le_log_det_hessianMatrix`](https://prove2.me/theorems/6d69beca-a1f9-48e2-959c-68716a21a551) · Next: [`exists_penalized_maximum_with_comparison`](https://prove2.me/theorems/511a8bb6-640f-477b-98fa-7c8e07f3450e).
--
--   [Source excerpt, lines 1412–1416](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1412-L1416) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1409-L1436 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.ae_exists_quadraticAt_expansion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

theorem FunctionalInequalities.Analysis.ae_exists_quadraticAt_expansion_readable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ ∃ g : EuclideanSpace ℝ (Fin n),
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by sorry
