-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hessianMatrix_quadraticAt_readable
-- name    : FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:09.375995+00:00
-- url     : https://prove2.me/theorems/facc6c9b-040a-4551-a141-72b34dae970f
-- title:
--   Hessian of a Quadratic Test Function
-- statement:
--   Let $A$ be a Hermitian real matrix indexed by $\mathrm{Fin}\ n$, let $x_0,b\in\mathbb R^n$, let $c\in\mathbb R$, and let $x\in\mathbb R^n$. For the quadratic test function `quadraticAt A x₀ b c`, its coordinate Hessian is constant:
--
--   $$\operatorname{hessianMatrix}(\operatorname{quadraticAt}(A,x_0,b,c))(x)=A.$$
--
--   This identity is pointwise in $x$ and is used to identify Hessians of quadratic touching functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hessianMatrix_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
--       (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
--       hessianMatrix (quadraticAt A x₀ b c) x = A
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Previous: [`det_hessianMatrix_le_of_lower_touch`](https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5) · Next: [`posDef_and_det_eq_of_quadratic_expansion`](https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b).
--
--   [Source excerpt, lines 833–835](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L833-L835) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L831-L847 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.hessianMatrix_quadraticAt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_readable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (quadraticAt A x₀ b c) x = A := by sorry
