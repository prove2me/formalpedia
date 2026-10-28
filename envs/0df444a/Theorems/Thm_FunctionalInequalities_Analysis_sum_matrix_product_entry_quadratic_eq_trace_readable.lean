-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_quadratic_eq_trace_readable
-- name    : FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:04.394163+00:00
-- url     : https://prove2.me/theorems/d887a248-417a-44cd-bedd-9dbc45f1c640
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_matrix_product_entry_quadratic_eq_trace {m n : ℕ}
--       (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
--       (R : Matrix (Fin m) (Fin m) ℝ)
--       (T : Fin m → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ k, (T k).IsSymm) :
--       (∑ p : Fin n × Fin n,
--         (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ
--           (R *ᵥ (fun k => (S * T k * S) p.1 p.2))) =
--         ∑ k : Fin m, ∑ l : Fin m, R k l * ((S * S) * T k * (S * S) * T l).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Supporting theorems: [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd).
--
--   Previous: [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd).
--
--   [Source excerpt, lines 148–155](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L148-L155) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L145-L180 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra

open Matrix
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.sum_matrix_product_entry_quadratic_eq_trace_readable {m n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (T : Fin m → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ k, (T k).IsSymm) :
    (∑ p : Fin n × Fin n,
      (fun k => (S * T k * S) p.1 p.2) ⬝ᵥ
        (R *ᵥ (fun k => (S * T k * S) p.1 p.2))) =
      ∑ k : Fin m, ∑ l : Fin m, R k l * ((S * S) * T k * (S * S) * T l).trace := by sorry
