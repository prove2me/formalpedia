-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_lines_ge_independent
-- name    : MunkresAlg.Assignment.lines_ge_independent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:15.445862+00:00
-- url     : https://prove2.me/theorems/266d4cc4-b71a-469b-aab5-e47d7975a948
-- title:
--   §1, Step 3, first bracket, p. 34 — lines containing all the zeros are at least the maximal number of independent zeros
-- statement:
--   Let $B$ be a real $n\times n$ matrix, and let $R$ be a set of rows and $C$ a set of columns such that every zero entry of $B$ lies in a row of $R$ or a column of $C$. Then, with $\nu(B)$ the maximal number of independent zeros of $B$,
--   $$
--   \nu(B)\le |R|+|C| .
--   $$
--   Any set of lines containing all the zeros of a matrix has at least as many lines as the maximal number of independent zeros.
--
--   This is the easy half of König's theorem in matrix form; it is the step that turns the count "covered lines = starred zeros" at Step 3 into the optimality of both.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 34, §1, Step 3, first bracket, third sentence

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic

namespace MunkresAlg.Assignment

/-- §1, Step 3, first bracket, p. 34: any set of lines containing all the zeros of a matrix has
at least as many lines as the maximal number of independent zeros. -/
theorem lines_ge_independent {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n))
    (hcov : CoversZeros B R C) :
    maxIndepZeros B ≤ R.card + C.card := by sorry

end MunkresAlg.Assignment
