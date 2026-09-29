-- Prove2me | Theorems.Thm_LinearOptimization_lp_dual_dual
-- name    : LinearOptimization.lp_dual_dual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:51:03.834603+00:00
-- url     : https://prove2.me/theorems/cc2d95d8-933d-47c0-be87-69c941e3f593
-- title:
--   The dual of the dual is the primal
-- statement:
--   **(Theorem 4.1)** If we transform the dual into an equivalent minimization problem and then form its dual, we obtain a problem equivalent to the original problem.
--
--   ("The dual of the dual is the primal.")
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.1, p. 144

import Definitions.Def_LinearOptimization_DualLP


/-- **Bertsimas & Tsitsiklis, Theorem 4.1 (p. 144).** The dual of the dual is the primal: the
equivalent-minimization dual operator is an involution on general-form
linear programs. -/

theorem LinearOptimization.lp_dual_dual {m n : ℕ} (P : GeneralFormLP m n) :
    dualLP (dualLP P) = P := by
  sorry
