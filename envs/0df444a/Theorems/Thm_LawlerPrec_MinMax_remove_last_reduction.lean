-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_remove_last_reduction
-- name    : LawlerPrec.MinMax.remove_last_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:45.848451+00:00
-- url     : https://prove2.me/theorems/2d3fe985-19b7-47c8-84fd-a4bc2b6d6f90
-- title:
--   §3 Sequencing Algorithm, p. 545 — an optimal sequence of the remaining jobs followed by $k$ is optimal
-- statement:
--   Let $J$ be a nonempty job set with non-negative processing times $a_j$ and monotone nondecreasing cost functions $c_j$, $S$ the jobs of $J$ not required to precede any others, $T = \sum_{j \in J} a_j$, and $k \in S$ with $c_k(T) = \min_{j \in S} c_j(T)$. Suppose $J \setminus \{k\}$ is nonempty and $\pi'$ is a minmax optimal sequence of the reduced problem on $J \setminus \{k\}$. Then
--
--   $$
--   (\pi', k) \text{ is a minmax optimal sequence of } J.
--   $$
--
--   This is the step of Lawler's algorithm "having removed $k$ from the problem, one finds a job which can be placed last among the remaining $n - 1$ jobs and second-to-last in the complete sequence": solving the reduced problem and appending $k$ solves the original one. The case $J = \{k\}$ is trivial and excluded by the nonemptiness hypothesis.
--
--   **Formalization Note** The reduced problem keeps the same processing times, costs and precedence relation, restricted to $J \setminus \{k\}$ (`J.erase k`). Non-negative processing times are an added, disclosed hypothesis.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 545, §3 Sequencing Algorithm, first paragraph

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsMinmaxOptimal
import Definitions.Def_LawlerPrec_MinMax_lastEligible

namespace LawlerPrec.MinMax

/-- §3 Sequencing Algorithm, p. 545, first paragraph: the reduction step. Let `k ∈ S` minimize
`c_j(T)` over `S`, `T = ∑_{j ∈ J} a_j`. If `l'` is a minmax optimal sequence of the remaining
jobs `J \ {k}` (assumed nonempty; the case `J = {k}` is trivial), then placing `k` after it gives
a minmax optimal sequence `l' ++ [k]` of `J`. -/
theorem remove_last_reduction {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (k : ι) (hk : k ∈ lastEligible prec J)
    (hmin : ∀ j ∈ lastEligible prec J, c k (∑ i ∈ J, a i) ≤ c j (∑ i ∈ J, a i))
    (hJ' : (J.erase k).Nonempty) (l' : List ι)
    (hl' : IsMinmaxOptimal a c prec (J.erase k) hJ' l') :
    IsMinmaxOptimal a c prec J hJ (l' ++ [k]) := by sorry

end LawlerPrec.MinMax
