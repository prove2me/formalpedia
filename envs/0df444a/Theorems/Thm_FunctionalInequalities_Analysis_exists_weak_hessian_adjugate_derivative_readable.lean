-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_weak_hessian_adjugate_derivative_readable
-- name    : FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:46.466372+00:00
-- url     : https://prove2.me/theorems/67ea3932-bb12-489c-b021-f170ae02b2db
-- title:
--   Weak Derivatives of Hessian Adjugates
-- statement:
--   Let $u:\mathbb{R}^n\to\mathbb{R}$ and let $T$ be a tensor giving locally $L^2$ weak directional derivatives of every Hessian entry $H_u{}_{ij}$. Assume every Hessian entry is globally in $L^{\infty}$. Then, for every coordinate direction $e_k$ and indices $i,j$, there exists a function $g$ such that
--
--   $$
--   \partial_k\operatorname{adj}(H_u)_{ij}=g
--   $$
--
--   in the weak sense, and $g$ belongs locally to $L^2$ on every compact set. The declaration is a cofactor-polynomial consequence of the supplied weak Hessian data and does not assume classical differentiability of the Hessian.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_weak_hessian_adjugate_derivative {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ}
--       {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
--       (hbound : ∀ r s : Fin n, MemLp (fun x => hessianMatrix u x r s)
--         (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hT : ∀ k i j : Fin n,
--         HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
--           (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--         ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => T x k i j) 2
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (k i j : Fin n) :
--       ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
--         HasWeakDerivAlong (fun x => (hessianMatrix u x).adjugate i j) g
--           (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
--         ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_det_of_locally_memLp_two`](https://prove2.me/theorems/33254f42-0c89-459e-bcd2-427b387a0099), [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552).
--
--   Previous: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574).
--
--   [Source excerpt, lines 1084–1100](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L1084-L1100) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L1083-L1132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Filter Metric Matrix

theorem FunctionalInequalities.Analysis.exists_weak_hessian_adjugate_derivative_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbound : ∀ r s : Fin n, MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (k i j : Fin n) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => (hessianMatrix u x).adjugate i j) g
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
