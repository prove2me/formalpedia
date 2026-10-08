-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step3_transformation
-- name    : MunkresAlg.Assignment.step3_transformation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:49.129667+00:00
-- url     : https://prove2.me/theorems/0a58f714-9f21-4e4e-bc71-1c7ed1e3dd63
-- title:
--   §1, Step 3, pp. 34–35 — h exists and is positive; non-covered −h, twice-covered +h; 0* and 0′ stay zeros; n_{k+1} ≥ n_k
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 3, with current matrix $A_k=(a_{ij})$, covered rows $R$ and covered columns $C$. Then there is a real $h$ with:
--
--   1. $h>0$, and $h$ is the smallest non-covered element: $h=a_{pq}$ for some $p\notin R,q\notin C$, and $h\le a_{ij}$ whenever $i\notin R$, $j\notin C$;
--   2. each starred and each primed zero is once-covered (lies in exactly one covered line);
--
--   and for every state $t$ reached from $s$ by the Step 3 move, with matrix $A_{k+1}=(a'_{ij})$:
--
--   3. $a'_{ij}=a_{ij}-h$ if $(i,j)$ is non-covered, $a'_{ij}=a_{ij}+h$ if it is twice-covered, and $a'_{ij}=a_{ij}$ if it is once-covered;
--   4. every starred and every primed zero of $s$ is still a zero of $A_{k+1}$;
--   5. $n_{k+1}\ge n_k$, where $n_k$ and $n_{k+1}$ are the maximal numbers of independent zeros of $A_k$ and $A_{k+1}$.
--
--   Part 1 rules out the algorithm getting stuck at Step 3, and part 5 is the monotonicity used in the finiteness argument.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), pp. 34–35, §1, Step 3 (second paragraph and second bracket)

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 3, pp. 34–35: at Step 3 the smallest non-covered element `h` exists and is positive;
the transformation decreases each non-covered element by `h`, increases each twice-covered element
by `h` and leaves each once-covered element unaltered; each starred and primed zero is
once-covered and is still a zero afterwards; and `n_{k+1} ≥ n_k`. -/
theorem step3_transformation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    ∃ h : ℝ, 0 < h ∧ (∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) ∧
      (∀ q, NonCovered s q → h ≤ s.A q.1 q.2) ∧
      (∀ p ∈ s.starred ∪ s.primed,
        (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
      ∀ t, Step s t →
        (∀ i j, i ∉ s.rowCov → j ∉ s.colCov → t.A i j = s.A i j - h) ∧
        (∀ i j, i ∈ s.rowCov → j ∈ s.colCov → t.A i j = s.A i j + h) ∧
        (∀ i j, (i ∈ s.rowCov ∧ j ∉ s.colCov) ∨ (i ∉ s.rowCov ∧ j ∈ s.colCov) →
          t.A i j = s.A i j) ∧
        (∀ p ∈ s.starred ∪ s.primed, t.A p.1 p.2 = 0) ∧
        maxIndepZeros s.A ≤ maxIndepZeros t.A := by sorry

end MunkresAlg.Assignment
