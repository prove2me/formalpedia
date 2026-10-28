-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_mul_eq_trace_readable
-- name    : FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:04.292823+00:00
-- url     : https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd
-- title:
--   Entrywise Matrix Product Trace Identity
-- statement:
--   This statement is a finite-dimensional trace-algebra identity.
--
--   Let S,A,D be real matrices indexed by `Fin n`. Assume S and D are symmetric. Then
--
--   $$\sum_{i,j}(SAS)_{ij}(SDS)_{ij}
--   =\operatorname{tr}\bigl((SS)A(SS)D\bigr).$$
--
--   No symmetry assumption is imposed on A.
--
--   This identity converts an entrywise product of symmetric matrix expressions into a trace expression and is useful in finite trace-energy calculations.
--
--   **Formalization Note** All products are ordinary real matrix products over `Fin n`; the theorem is an equality, not an inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_matrix_product_entry_mul_eq_trace {n : ℕ}
--       (S A D : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) (hD : D.IsSymm) :
--       (∑ p : Fin n × Fin n, (S * A * S) p.1 p.2 * (S * D * S) p.1 p.2) =
--         ((S * S) * A * (S * S) * D).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Previous: [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75) · Next: [`sum_matrix_product_entry_quadratic_eq_trace`](https://prove2.me/theorems/d887a248-417a-44cd-bedd-9dbc45f1c640).
--
--   [Source excerpt, lines 121–124](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L121-L124) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L120-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra

theorem FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable {n : ℕ}
    (S A D : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) (hD : D.IsSymm) :
    (∑ p : Fin n × Fin n, (S * A * S) p.1 p.2 * (S * D * S) p.1 p.2) =
      ((S * S) * A * (S * S) * D).trace := by sorry
