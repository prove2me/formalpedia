-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_move_last_maxCost_le
-- name    : LawlerPrec.MinMax.move_last_maxCost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:14:27.836531+00:00
-- url     : https://prove2.me/theorems/b5eebf6d-a137-41b2-a6b4-f529c2ac91d0
-- title:
--   §2, proof of the Theorem, p. 544 — moving a least-cost job of $S$ last does not raise the maximum cost
-- statement:
--   Let $J$ be a nonempty job set with non-negative processing times $a_j$ and monotone nondecreasing cost functions $c_j$, and let $T = \sum_{j \in J} a_j$. Let $\pi'$ be a sequence of $J$ observing the precedence constraints, with last job $k'$, and let $k \in S(J)$ satisfy $c_k(T) \le c_{k'}(T)$. If $\pi$ is obtained from $\pi'$ by moving $k$ to the last position, then
--
--   $$
--   \max_{j \in J} c_j\bigl(C_j(\pi)\bigr) \;\le\; \max_{j \in J} c_j\bigl(C_j(\pi')\bigr).
--   $$
--
--   This is the conclusion of Lawler's proof: the exchange of $\pi' = (A, k, B, k')$ for $\pi = (A, B, k', k)$ does not increase the maximum incurred cost. The case $k' = k$ is allowed and trivial.
--
--   **Formalization Note** $\pi$ is `l.erase k ++ [k]`; the last job of $\pi'$ is given by `l.getLast? = some k'`. Non-negative processing times are an added, disclosed hypothesis (see `move_last_completion_le`). Monotonicity is required of the cost functions of jobs in $J$ only.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §2 Sequencing Theorem, PROOF, fourth paragraph

import Mathlib
import Definitions.Def_MooreLateJobs_MaxDeferral_maxCost
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerPrec_MinMax_lastEligible

namespace LawlerPrec.MinMax

/-- §2, proof of the Theorem, p. 544, fourth paragraph: if `π′ = l` observes the precedence
constraints and ends with job `k′`, and `k ∈ S` satisfies `c_k(T) ≤ c_{k′}(T)` with
`T = ∑_{j ∈ J} a_j`, then the maximum incurred cost of `π = l.erase k ++ [k]` is no greater
than that of `π′`. Processing times are non-negative and the costs `c_j` are monotone
nondecreasing. (`k′ = k` is allowed and trivial.) -/
theorem move_last_maxCost_le {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (ha : ∀ j ∈ J, 0 ≤ a j)
    (hc : ∀ j ∈ J, Monotone (c j)) (l : List ι) (hl : IsFeasible prec J l) (k k' : ι)
    (hlast : l.getLast? = some k') (hk : k ∈ lastEligible prec J)
    (hkk' : c k (∑ j ∈ J, a j) ≤ c k' (∑ j ∈ J, a j)) :
    MooreLateJobs.MaxDeferral.maxCost a c J hJ (l.erase k ++ [k]) ≤
      MooreLateJobs.MaxDeferral.maxCost a c J hJ l := by sorry

end LawlerPrec.MinMax
