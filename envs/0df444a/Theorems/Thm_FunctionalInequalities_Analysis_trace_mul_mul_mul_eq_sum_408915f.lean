-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_408915f
-- name    : FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:42.617373+00:00
-- url     : https://prove2.me/theorems/e6fc90c6-b40e-49b9-9889-34fd22631f86
-- title:
--   Trace Expansion for Four Matrix Factors
-- statement:
--   This is an algebraic expansion of the trace of a product of four real square matrices.
--
--   Let $n$ be a natural number and let $A,H,B,J$ be matrices in $M_n(\mathbb R)$. Then:
--
--   $$
--   \operatorname{tr}(AHBJ)=\sum_{a,b,c,d\in\operatorname{Fin}(n)}(A_{ab}B_{cd})(H_{bc}J_{da}).
--   $$
--
--   The Lean definition involved is `trace_mul_mul_mul_eq_sum`. This identity is a reusable coordinate formula for trace quartics and does not require symmetry, invertibility, or positivity of any matrix.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L86-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, declaration `FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum`; the repository is private at upload time).

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TraceFourProduct

theorem FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_408915f {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
    (A * H * B * J).trace =
      ∑ q : Fin n × Fin n × Fin n × Fin n,
        (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
          (H q.2.1 q.2.2.1 * J q.2.2.2 q.1) := by sorry
