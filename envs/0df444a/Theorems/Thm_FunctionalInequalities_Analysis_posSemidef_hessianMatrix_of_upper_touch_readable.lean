-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_hessianMatrix_of_upper_touch_readable
-- name    : FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:46.646392+00:00
-- url     : https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d
-- title:
--   Semidefinite Hessian at an Upper Touch
-- statement:
--   Let $u,\psi:\mathbb R^n\to\mathbb R$, with $u$ convex. If $\psi\in C^2$ at $x_0$, $u(x_0)=\psi(x_0)$, and $u(x)\le\psi(x)$ in a neighborhood of $x_0$, then the coordinate Hessian of $\psi$ at $x_0$ is positive semidefinite:
--
--   $$\operatorname{hessianMatrix}(\psi)(x_0)\succeq0.$$
--
--   This is a pointwise viscosity touching principle for convex functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem posSemidef_hessianMatrix_of_upper_touch {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀)
--       (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
--       (hessianMatrix ψ x₀).PosSemidef
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`directional_second_deriv_nonneg`](https://prove2.me/theorems/86f74169-4ea8-4fc0-a5ef-90fee5ab8c8b).
--
--   Previous: [`directional_second_deriv_nonneg`](https://prove2.me/theorems/86f74169-4ea8-4fc0-a5ef-90fee5ab8c8b) · Next: [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd).
--
--   [Source excerpt, lines 149–152](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L149-L152) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L147-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_readable {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (hessianMatrix ψ x₀).PosSemidef := by sorry
