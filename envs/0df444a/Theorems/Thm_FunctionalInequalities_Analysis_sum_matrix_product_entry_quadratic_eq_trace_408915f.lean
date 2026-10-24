-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_quadratic_eq_trace_408915f
-- name    : FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:04.775724+00:00
-- url     : https://prove2.me/theorems/c2e4b6ab-6519-4bfb-bfb4-d42f56ffe589
-- title:
--   Entrywise Quadratic Energy Trace Identity
-- statement:
--   This statement converts a family of entrywise quadratic energies into a trace sum.
--
--   Let S be a symmetric real n-by-n matrix. Let R be an arbitrary real m-by-m matrix, and let Tₖ be symmetric real n-by-n matrices indexed by `Fin m`. For each pair of matrix-entry indices p, define the vector whose k-th coordinate is $(ST_kS)_p$. Then
--
--   $$\sum_p (ST_{\bullet}S)_p\mathbin{\cdot}\bigl(R(ST_{\bullet}S)_p\bigr)
--   =\sum_{k,l}R_{kl}\operatorname{tr}\bigl((SS)T_k(SS)T_l\bigr).$$
--
--   This is a finite algebraic identity for entrywise inverse-quadratic energies and trace energies.
--
--   **Formalization Note** R need not be symmetric or positive; symmetry is required only for S and every Tₖ.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L145-L180 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace`; the repository is private at upload time).

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
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace_408915f {m n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (T : Fin m → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ k, (T k).IsSymm) :
    (∑ p : Fin n × Fin n,
      (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ
        (R *ᵥ (fun k => (S * T k * S) p.1 p.2))) =
      ∑ k : Fin m, ∑ l : Fin m, R k l * ((S * S) * T k * (S * S) * T l).trace := by sorry
