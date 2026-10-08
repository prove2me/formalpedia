-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_sequencing_theorem
-- name    : LawlerPrec.MinMax.sequencing_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:31.220659+00:00
-- url     : https://prove2.me/theorems/dba11ee6-9609-4886-a254-990ac9f0a87d
-- title:
--   THEOREM (§2 Sequencing Theorem), p. 544 — some minmax optimal sequence has a least-cost job of $S$ last
-- statement:
--   Let $J$ be a nonempty finite set of jobs with non-negative processing times $a_j$, monotone nondecreasing cost functions $c_j$, and arbitrary precedence constraints, and suppose some sequence of $J$ observes the constraints. Let $S$ be the set of jobs of $J$ not required to precede any others, $T = \sum_{j \in J} a_j$, and let $k \in S$ satisfy
--
--   $$
--   c_k(T) \;=\; \min_{j \in S} c_j(T).
--   $$
--
--   Then there exists a minmax optimal sequence in which job $k$ is last.
--
--   This is the paper's only labelled result. It reduces the choice of the last job of an optimal sequence to a comparison of the eligible jobs' costs at the fixed time $T$, independently of how the other jobs are ordered.
--
--   **Formalization Note** Two hypotheses are added and disclosed: non-negative processing times (durations; the paper's proof uses them) and the existence of a feasible sequence, which "there exists a minmax optimal sequence" presupposes (with a cycle in the constraints, no sequence observes them, while $S$ can still be nonempty). The minimum is encoded as $k \in S$ and $c_k(T) \le c_j(T)$ for all $j \in S$; ties are allowed.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §2 Sequencing Theorem, THEOREM

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsMinmaxOptimal
import Definitions.Def_LawlerPrec_MinMax_lastEligible

namespace LawlerPrec.MinMax

/-- THEOREM (§2 Sequencing Theorem, Lawler 1973, p. 544). Let `S = lastEligible prec J` be the jobs
not required to precede any others, `T = ∑_{j ∈ J} a_j`, and `k ∈ S` with
`c_k(T) = min_{j ∈ S} c_j(T)`. If some sequence of `J` observes the precedence constraints, then
there is a minmax optimal sequence in which job `k` is last. -/
theorem sequencing_theorem {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (hfeas : ∃ l : List ι, IsFeasible prec J l) (k : ι)
    (hk : k ∈ lastEligible prec J)
    (hmin : ∀ j ∈ lastEligible prec J, c k (∑ i ∈ J, a i) ≤ c j (∑ i ∈ J, a i)) :
    ∃ l : List ι, IsMinmaxOptimal a c prec J hJ l ∧ l.getLast? = some k := by sorry

end LawlerPrec.MinMax
