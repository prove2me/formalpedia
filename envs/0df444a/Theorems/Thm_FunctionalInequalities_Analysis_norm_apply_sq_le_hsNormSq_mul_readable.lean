-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_norm_apply_sq_le_hsNormSq_mul_readable
-- name    : FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:06.579026+00:00
-- url     : https://prove2.me/theorems/3aa78c22-bf8d-4c99-aea7-40e318280ade
-- title:
--   Hilbert–Schmidt Bound On Operator Application
-- statement:
--   This statement bounds the norm of an operator applied to a vector.
--
--   Let n be a natural number, let M be a continuous linear endomorphism of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let x be a vector. Then
--
--   $$\|Mx\|^2\leq\|M\|_{HS}^2\,\|x\|^2,$$
--
--   where `hsNormSq M` is the squared Hilbert–Schmidt norm.
--
--   This is a standard finite-dimensional estimate useful for Lyapunov and cutoff bounds.
--
--   **Formalization Note** The statement uses the canonical Euclidean basis and includes all natural numbers n.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_apply_sq_le_hsNormSq_mul (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (x : EuclideanSpace ℝ (Fin n)) : ‖M x‖ ^ 2 ≤ hsNormSq M * ‖x‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34).
--
--   Next: [`opNorm_sq_le_hsNormSq`](https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762).
--
--   [Source excerpt, lines 76–77](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L76-L77) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L75-L103 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt

variable {n : ℕ}

theorem FunctionalInequalities.Analysis.norm_apply_sq_le_hsNormSq_mul_readable (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ‖M x‖ ^ 2 ≤ hsNormSq M * ‖x‖ ^ 2 := by sorry
