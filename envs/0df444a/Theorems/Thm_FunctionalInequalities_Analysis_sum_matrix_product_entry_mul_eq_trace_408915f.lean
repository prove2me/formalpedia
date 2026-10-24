-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_mul_eq_trace_408915f
-- name    : FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:06.038988+00:00
-- url     : https://prove2.me/theorems/3c87d3a4-165b-449b-a59d-ecf1206ba5e5
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L120-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace`; the repository is private at upload time).

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open Matrix
section MatrixProductEntryTrace
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_408915f {n : ℕ}
    (S A D : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) (hD : D.IsSymm) :
    (∑ p : Fin n × Fin n, (S * A * S) p.1 p.2 * (S * D * S) p.1 p.2) =
      ((S * S) * A * (S * S) * D).trace := by sorry
