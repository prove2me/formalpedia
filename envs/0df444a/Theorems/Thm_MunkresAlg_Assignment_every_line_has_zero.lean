-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_every_line_has_zero
-- name    : MunkresAlg.Assignment.every_line_has_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:04.838742+00:00
-- url     : https://prove2.me/theorems/f17e71db-fecf-4262-9765-bcaff8d39baf
-- title:
--   §1, p. 36 — after the Preliminaries each row and column contains a zero, and this never changes
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be any state reachable by Munkres' algorithm from $A$ (including the start states), with current matrix $B=(b_{ij})$. Then every row and every column of $B$ contains a zero:
--   $$
--   \forall i\ \exists j:\ b_{ij}=0, \qquad \forall j\ \exists i:\ b_{ij}=0 .
--   $$
--
--   The paper uses this fact in its operation count; it holds after the Preliminaries and is preserved by the Step 3 transformation.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 36, §1

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, p. 36: after the Preliminaries each row and each column of the matrix contains at least
one zero, and this never changes. -/
theorem every_line_has_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) :
    (∀ i, ∃ j, s.A i j = 0) ∧ (∀ j, ∃ i, s.A i j = 0) := by sorry

end MunkresAlg.Assignment
