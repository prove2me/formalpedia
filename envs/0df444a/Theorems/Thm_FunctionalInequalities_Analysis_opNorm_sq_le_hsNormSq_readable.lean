-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_opNorm_sq_le_hsNormSq_readable
-- name    : FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:02.891975+00:00
-- url     : https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762
-- title:
--   Operator Norm Bounded By Hilbert–Schmidt Norm
-- statement:
--   This statement compares two norms of a finite-dimensional operator.
--
--   Let M be a continuous linear endomorphism of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Then
--
--   $$\|M\|_{op}^2\leq\|M\|_{HS}^2,$$
--
--   where `hsNormSq M` denotes the squared Hilbert–Schmidt norm.
--
--   This is a basic norm comparison reusable in finite-dimensional operator estimates.
--
--   **Formalization Note** The result is stated for every natural number n and uses the operator norm supplied by the continuous-linear-map structure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem opNorm_sq_le_hsNormSq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
--       ‖M‖ ^ 2 ≤ hsNormSq M
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34).
--
--   Supporting theorems: [`norm_apply_sq_le_hsNormSq_mul`](https://prove2.me/theorems/3aa78c22-bf8d-4c99-aea7-40e318280ade).
--
--   Previous: [`norm_apply_sq_le_hsNormSq_mul`](https://prove2.me/theorems/3aa78c22-bf8d-4c99-aea7-40e318280ade) · Next: [`sum_inner_apply_le_sqrt_hsNormSq_mul`](https://prove2.me/theorems/9a0d0118-09fb-42ba-8956-a35ad70bd1c0).
--
--   [Source excerpt, lines 106–107](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L106-L107) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L105-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt

variable {n : ℕ}

theorem FunctionalInequalities.Analysis.opNorm_sq_le_hsNormSq_readable (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖M‖ ^ 2 ≤ hsNormSq M := by sorry
