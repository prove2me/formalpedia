-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_directional_second_deriv_nonneg_readable
-- name    : FunctionalInequalities.Analysis.directional_second_deriv_nonneg_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:59.199682+00:00
-- url     : https://prove2.me/theorems/86f74169-4ea8-4fc0-a5ef-90fee5ab8c8b
-- title:
--   Nonnegative Directional Second Derivative at an Upper Touch
-- statement:
--   This technical lemma concerns a convex function $u:\mathbb R^n\to\mathbb R$ and a test function $\psi$. If $u$ is convex, $\psi\in C^2$ at $x_0$, $u(x_0)=\psi(x_0)$, and $u\le\psi$ almost everywhere in a neighborhood of $x_0$, then every direction $v\in\mathbb R^n$ satisfies
--
--   $$0\le D^2\psi(x_0)[v,v].$$
--
--   The result is a one-dimensional directional form of the positive-semidefinite Hessian conclusion used by the public touching lemma.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma directional_second_deriv_nonneg
--       {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)}
--       (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
--       (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       0 ≤ bilinearIteratedFDerivTwo ℝ ψ x₀ v v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Next: [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d).
--
--   [Source excerpt, lines 26–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L26-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L26-L145 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.directional_second_deriv_nonneg`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open Set Metric Filter
open scoped RealInnerProductSpace Topology

lemma FunctionalInequalities.Analysis.directional_second_deriv_nonneg_readable
    {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by sorry
