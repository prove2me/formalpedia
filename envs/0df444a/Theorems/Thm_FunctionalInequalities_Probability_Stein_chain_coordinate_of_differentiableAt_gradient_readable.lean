-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_chain_coordinate_of_differentiableAt_gradient_readable
-- name    : FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:42.343657+00:00
-- url     : https://prove2.me/theorems/5a18cc05-1ac8-4293-a020-60dea2d6f206
-- title:
--   Coordinate Chain Rule Through the Gradient Map
-- statement:
--   This statement gives a coordinate chain rule for a composition with a gradient map.
--
--   Let $n\in\mathbb N$ and let $u,f:\mathbb R^n\to\mathbb R$ be $C^1$. At a point $y\in\mathbb R^n$, assume that $∇u$ is differentiable at $y$. For every coordinate $i\in\operatorname{Fin}(n)$,
--
--   $$
--   D_{e_i}(f\circ∇u)(y)
--   =
--   \sum_j (\nabla^2u(y))_{ij}\,(\nabla f(\nabla u(y)))_j.
--   $$
--
--   Here `hessianMatrix u y` is the matrix used for the weak Hessian coordinates. The result is a finite-dimensional pointwise identity and makes no global invertibility claim about $∇u$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Stein`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem chain_coordinate_of_differentiableAt_gradient {n : ℕ}
--       {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
--       (hf : ContDiff ℝ 1 f) {y : EuclideanSpace ℝ (Fin n)}
--       (hy : DifferentiableAt ℝ (gradient u) y) (i : Fin n) :
--       fderiv ℝ (f ∘ gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
--         ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Previous: [`memLp_cutoff_mul_hessianMatrix_entry`](https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1).
--
--   [Source excerpt, lines 504–509](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L504-L509) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.7 (Fathi [29, Theorem 2.3]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L501-L535 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian

set_option maxHeartbeats 400000

theorem FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient_readable {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (hf : ContDiff ℝ 1 f) {y : EuclideanSpace ℝ (Fin n)}
    (hy : DifferentiableAt ℝ (gradient u) y) (i : Fin n) :
    fderiv ℝ (f ∘ gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j := by sorry
