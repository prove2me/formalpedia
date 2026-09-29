-- Prove2me | Theorems.Thm_MathematicalRelativity_trace_sq_le_card_mul_trace_transpose_mul
-- name    : MathematicalRelativity.trace_sq_le_card_mul_trace_transpose_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T15:15:37.020965+00:00
-- url     : https://prove2.me/theorems/3741019a-df2e-4cc0-9a13-bbd00ddda0f4
-- title:
--   $(\operatorname{tr} A)^2 \le n\,\operatorname{tr}(A^{t}A)$
-- statement:
--   For every real $n \times n$ matrix $A$,
--   $$ (\operatorname{tr} A)^{2} \;\le\; n \operatorname{tr}(A^{t}A) . $$
--   This is the Cauchy–Schwarz inequality applied to the diagonal of $A$; in the proof of the null focusing proposition it converts the shear term into the inequality $\beta_{BA}\beta^{AB} \ge \tfrac{1}{2}\theta^{2}$, and its timelike analogue gives $\tfrac{1}{3}\theta^{2}$.
-- source:
--   J. Natário, Mathematical Relativity, arXiv:2003.02855, p. 82, Chapter 4, proof of Proposition 6.2 (inequality (tr A)^2 <= n tr(A^t A))

import Mathlib

namespace MathematicalRelativity

theorem trace_sq_le_card_mul_trace_transpose_mul
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.trace) ^ 2 ≤ (n : ℝ) * (A.transpose * A).trace := by
  sorry

end MathematicalRelativity
