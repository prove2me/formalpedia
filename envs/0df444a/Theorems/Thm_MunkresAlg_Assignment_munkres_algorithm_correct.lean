-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_munkres_algorithm_correct
-- name    : MunkresAlg.Assignment.munkres_algorithm_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:16.874998+00:00
-- url     : https://prove2.me/theorems/1b6039e9-159f-45cc-a989-2226da87004f
-- title:
--   §1, pp. 33–35 — Munkres' algorithm terminates on every real matrix, never gets stuck, and ends with an optimal assignment
-- statement:
--   Let $A=(x_{ij})$ be any real $n\times n$ matrix, $x_{ij}$ being the cost of assigning row (man) $i$ to column (job) $j$. Consider Munkres' algorithm on $A$, with all of its free choices (the order in which the Preliminaries consider the zeros, and the non-covered zero primed in Step 1). Then:
--
--   1. **the algorithm can start:** there is a start state for $A$;
--   2. **every run is finite:** from every start state there is no infinite sequence of moves;
--   3. **no run gets stuck:** every reachable state that is not done has a next move;
--   4. **the output is optimal:** at every reachable done state the starred zeros are exactly the positions $\{(\sigma(r),r) : r=1,\dots,n\}$ of a permutation $\sigma$, and
--   $$
--   \sum_{r} x_{\sigma(r)\,r}\ \le\ \sum_{r} x_{\tau(r)\,r}\qquad\text{for every permutation } \tau .
--   $$
--
--   Together, 2 and 3 say every run reaches the done state, and 4 says that it then holds a set of $n$ independent elements of $A$ with minimum sum, which is the assignment problem of p. 32. Optimality is with respect to the original matrix $A$, not the transformed one.
--
--   **Formalization Note** The entries of $A$ are arbitrary reals: the integrality assumption of p. 32 is withdrawn on p. 35. Finiteness of every run is stated as accessibility (`Acc`) of the start state for the reversed move relation. The test "if all columns are covered, stop" is also applied right after the Preliminaries (the page goes to Step 1 unconditionally there, after which Step 3 would have no non-covered element if the Preliminaries already starred $n$ zeros). For $n=0$ the start state is done and the empty permutation is optimal.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), pp. 33–35, §1 (algorithm pp. 33–34; problem p. 32; finiteness for real matrices p. 35)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- Munkres (1957), §1, pp. 33–35: correctness of the assignment algorithm on every real
`n × n` matrix `A`. The Preliminaries can be carried out; every run is finite; no run gets stuck
before it stops; and when it stops, the starred zeros are the positions `(σ r, r)` of a
permutation `σ` that is an optimal assignment for the original matrix `A`. -/
theorem munkres_algorithm_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ s₀, IsStart A s₀) ∧
    (∀ s₀, IsStart A s₀ → Acc (fun t s => Step s t) s₀) ∧
    (∀ s, Reachable A s → s.phase ≠ Phase.done → ∃ t, Step s t) ∧
    (∀ s, Reachable A s → s.phase = Phase.done →
      ∃ σ : Equiv.Perm (Fin n), s.starred = Finset.univ.image (fun r => (σ r, r)) ∧
        HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ) := by sorry

end MunkresAlg.Assignment
