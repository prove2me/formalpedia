-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step3_sum_decrease
-- name    : MunkresAlg.Assignment.step3_sum_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:16.349663+00:00
-- url     : https://prove2.me/theorems/82f72e58-29e3-4852-aa41-13bbacc2a204
-- title:
--   §1, Step D (p. 33) for Step 3 — the sum of the elements decreases by n(n − n_k)h
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 3, with matrix $A_k=(a_{ij})$. Let $h$ be the smallest non-covered element of $A_k$, and let $t$ be a state reached from $s$ by the Step 3 move, with matrix $A_{k+1}=(a'_{ij})$. With $n_k$ the maximal number of independent zeros of $A_k$,
--   $$
--   \sum_{i,j} a'_{ij}=\sum_{i,j} a_{ij}-n\,(n-n_k)\,h .
--   $$
--
--   Step 3 is the transformation of Step C of Flood's outline, and Step D states this decrease; for integer matrices it gives the original finiteness argument.
--
--   **Formalization Note** $n-n_k$ is computed in the reals; it is non-negative because $n_k\le n$.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 33, §1, Step D (applied to Step 3, p. 34, which 'is the same transformation as is specified in Step C')

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step D (p. 33) for the transformation of Step 3: the sum of the elements of the matrix
decreases by `n (n − n_k) h`, where `n_k` is the maximal number of independent zeros before the
transformation and `h` the smallest non-covered element. -/
theorem step3_sum_decrease {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n) (h : ℝ)
    (hs : Reachable A s) (hph : s.phase = Phase.step3)
    (hmin : ∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) (hle : ∀ q, NonCovered s q → h ≤ s.A q.1 q.2)
    (hst : Step s t) :
    ∑ i, ∑ j, t.A i j =
      ∑ i, ∑ j, s.A i j - (n : ℝ) * ((n : ℝ) - (maxIndepZeros s.A : ℝ)) * h := by sorry

end MunkresAlg.Assignment
