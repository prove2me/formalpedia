-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convolution_hessian_integral_readable
-- name    : FunctionalInequalities.Analysis.convolution_hessian_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:00.716989+00:00
-- url     : https://prove2.me/theorems/71cd5614-d749-4ac1-8ee0-bcd17a10ea5c
-- title:
--   Convolution Hessian Quadratic Form Integral Formula
-- statement:
--   This is a technical identity relating the Hessian of a convolution to an integral of directional second derivatives.
--
--   Let $n\in\mathbb N$, let $\rho,u:\mathbb R^n\to\mathbb R$, and assume that $\rho$ is $C^2$ with compact support and that $u$ is continuous. For every $x,v\in\mathbb R^n$, the quadratic form of the coordinate Hessian of the convolution $\rho*u$ satisfies
--
--   $$
--   \left\langle v,\nabla^2(\rho*u)(x)v\right\rangle
--   =
--   \int_{\mathbb R^n}u(y)\,D^2\!\bigl[z\mapsto\rho(x-z)\bigr](y)[v,v] \,dy.
--   $$
--
--   Here `hessianMatrix` denotes the coordinate Hessian and `convolution` uses Lebesgue volume measure. The result provides the integral representation needed to transfer pointwise second-order information through mollification.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma convolution_hessian_integral {n : ℕ}
--       {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hu : Continuous u)
--       (x v : EuclideanSpace ℝ (Fin n)) :
--       ⟪v, Matrix.toEuclideanLin
--         (hessianMatrix (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v⟫ =
--         ∫ y, u y * iteratedFDeriv ℝ 2 (fun z => ρ (x - z)) y (fun _ => v)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`tendsto_integral_secondDifference_mul`](https://prove2.me/theorems/4354b6fd-00d6-4dd4-9dfb-0b7b24838470), [`expansion_secondDifference`](https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe), [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd), [`local_taylor_two`](https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203).
--
--   Previous: [`expansion_secondDifference`](https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe) · Next: [`trace_integral_bound`](https://prove2.me/theorems/d9cb05da-6288-4525-adcd-78dfcf3313ac).
--
--   [Source excerpt, lines 1091–1097](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1091-L1097) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1091-L1151 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.convolution_hessian_integral`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

lemma FunctionalInequalities.Analysis.convolution_hessian_integral_readable {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hu : Continuous u)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin
      (hessianMatrix (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v⟫ =
      ∫ y, u y * iteratedFDeriv ℝ 2 (fun z => ρ (x - z)) y (fun _ => v) := by sorry
