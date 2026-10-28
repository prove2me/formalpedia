-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable
-- name    : FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:36.323871+00:00
-- url     : https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6
-- title:
--   Coordinatewise Hessian Bound from Gradient Lipschitzness
-- statement:
--   This declaration gives a coordinatewise weak-Hessian estimate and is listed as partially related to the Key moment-map Hessian bound, Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $n$ be a natural number, let $u : \mathbb{R}^n \to \mathbb{R}$ be represented by `EuclideanSpace ℝ (Fin n)`, and let $G$ be a nonnegative real number represented by `NNReal`. Assume that the gradient map $\nabla u$ is $G$-Lipschitz with respect to the Euclidean norm. Then, for every point $x \in \operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}(n))$ and every pair of coordinate indices $i,j \in \operatorname{Fin}(n)$, the corresponding entry of `hessianMatrix u x` satisfies
--
--   $$
--   \left\|\operatorname{hessianMatrix}(u,x,i,j)\right\| \leq G.
--   $$
--
--   Here the norm on the real-valued Hessian entry is the usual absolute-value norm, and $G$ on the right-hand side denotes the coercion from `NNReal` to $\mathbb{R}$. This is a technical coordinatewise estimate that can be reused whenever a weak Hessian is defined through the derivative of a Lipschitz gradient.
--
--   **Formalization Note** The statement applies in finite-dimensional Euclidean space for every natural number $n$, including $n=0$, and does not assert classical $C^2$ regularity or differentiability everywhere. The Hessian coordinates are expressed using the Lean definition `hessianMatrix`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Stein`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_hessianMatrix_entry_le_of_lipschitz_gradient {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
--       (hG : LipschitzWith G (gradient u))
--       (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
--       ‖hessianMatrix u x i j‖ ≤ (G : ℝ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Previous: [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3) · Next: [`memLp_cutoff_mul_hessianMatrix_entry`](https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1).
--
--   [Source excerpt, lines 402–406](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L402-L406) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L400-L420 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian

theorem FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖hessianMatrix u x i j‖ ≤ (G : ℝ) := by sorry
