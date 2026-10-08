-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step3_maximal_minimal
-- name    : MunkresAlg.Assignment.step3_maximal_minimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:30.547681+00:00
-- url     : https://prove2.me/theorems/6d6fe7b5-37ae-4281-85ee-d4c5ddb28335
-- title:
--   §1, Step 3, first bracket, p. 34 — at Step 3 the starred zeros are a maximal independent set and the covered lines a minimal cover
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 3, with current matrix $B$, covered rows $R$, covered columns $C$ and starred zeros $S$. Then:
--
--   1. all the zeros of $B$ are covered: every $b_{ij}=0$ has $i\in R$ or $j\in C$;
--   2. each starred zero is covered by precisely one line: for $(i,j)\in S$, exactly one of $i\in R$, $j\in C$ holds;
--   3. there are exactly as many covered lines as starred zeros: $|R|+|C|=|S|$;
--   4. the starred zeros form a maximal set of independent zeros: $S$ is a set of independent zeros of $B$ and $|S|=\nu(B)$;
--   5. the covered lines form a minimal set of lines containing all the zeros: for every $R',C'$ containing all the zeros of $B$, $|R|+|C|\le |R'|+|C'|$.
--
--   Here $\nu(B)$ is the maximal number of independent zeros. Steps 1 and 2 thus carry out Step B of Flood's outline, finding a minimal cover and a maximal independent set.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 34, §1, Step 3, first bracket

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 3, first bracket, p. 34: at Step 3 all zeros are covered, each starred zero is
covered by exactly one line, there are as many covered lines as starred zeros, the starred zeros
form a maximum set of independent zeros, and the covered lines form a minimum set of lines
containing all the zeros. -/
theorem step3_maximal_minimal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    CoversZeros s.A s.rowCov s.colCov ∧
    (∀ p ∈ s.starred, (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
    s.rowCov.card + s.colCov.card = s.starred.card ∧
    (IsIndepZeros s.A s.starred ∧ s.starred.card = maxIndepZeros s.A) ∧
    (∀ R C : Finset (Fin n), CoversZeros s.A R C →
      s.rowCov.card + s.colCov.card ≤ R.card + C.card) := by sorry

end MunkresAlg.Assignment
