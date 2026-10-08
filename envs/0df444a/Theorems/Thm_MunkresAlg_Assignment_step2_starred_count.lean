-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step2_starred_count
-- name    : MunkresAlg.Assignment.step2_starred_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:25.709011+00:00
-- url     : https://prove2.me/theorems/0cc2f025-aa7c-4354-b9a3-709ce8799c72
-- title:
--   §1, Step 2, second bracket, p. 34 — after the exchange the starred zeros are independent and larger by one
-- statement:
--   Let $A$ be a real $n\times n$ matrix, let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 2, and let $t$ be the state after the Step 2 move (unstar each starred zero of the sequence, star each primed zero of the sequence, reset the marks). Then the starred zeros of $t$ form a set of independent zeros of the matrix of $t$, and
--   $$
--   \#\{\text{starred zeros of } t\}=\#\{\text{starred zeros of } s\}+1 .
--   $$
--
--   Each pass through Step 2 therefore adds one independent zero; as there can be at most $n$, Step 2 occurs at most $n$ times in a run.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 34, §1, Step 2, second bracket

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 2, second bracket, p. 34: after exchanging stars and primes along the sequence, the
starred zeros are independent zeros and there is one more of them. -/
theorem step2_starred_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀)
    (hst : Step s t) :
    IsIndepZeros t.A t.starred ∧ t.starred.card = s.starred.card + 1 := by sorry

end MunkresAlg.Assignment
