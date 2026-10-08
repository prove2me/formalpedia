-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_prelim_starred_independent
-- name    : MunkresAlg.Assignment.prelim_starred_independent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:31:11.037989+00:00
-- url     : https://prove2.me/theorems/b88b67ca-8421-4025-979b-f891d22123c2
-- title:
--   §1, Preliminaries, bracket, p. 33 — the zeros starred in the Preliminaries are independent
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be a start state of Munkres' algorithm for $A$, obtained from the Preliminaries with any order of considering the zeros. Then the starred zeros of $s$ form a set of independent zeros of the reduced matrix $A_1$ of $s$:
--   $$
--   \text{no two starred zeros lie in the same line, and } (A_1)_{ij}=0 \text{ for every starred } (i,j).
--   $$
--
--   This is the base case of the invariant that the starred zeros are always a set of independent zeros.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 33, §1, Preliminaries, bracket

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Preliminaries, p. 33: the zeros starred by the Preliminaries are independent (and are
zeros of the reduced matrix), whatever order the zeros are considered in. -/
theorem prelim_starred_independent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : IsStart A s) :
    IsIndepZeros s.A s.starred := by sorry

end MunkresAlg.Assignment
