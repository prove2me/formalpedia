-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_move_last_completion_le
-- name    : LawlerPrec.MinMax.move_last_completion_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:41.461612+00:00
-- url     : https://prove2.me/theorems/8834cc67-6477-4b00-a9a3-ad578a62fa79
-- title:
--   §2, proof of the Theorem, p. 544 — after moving $k$ last, no other job is completed later
-- statement:
--   Let $\pi'$ be a sequence of the job set $J$, the processing times $a_j$ non-negative, $k \in J$, and $\pi$ obtained from $\pi'$ by moving $k$ to the last position. Then every job other than $k$ completes in $\pi$ no later than in $\pi'$, and $k$ completes in $\pi$ at the total processing time $T$:
--
--   $$
--   C_j(\pi) \le C_j(\pi') \quad (j \in J,\ j \ne k), \qquad C_k(\pi) = T = \sum_{j \in J} a_j .
--   $$
--
--   This is the sentence "No job is completed later in $\pi$ than in $\pi'$, except job $k$" of Lawler's proof.
--
--   **Formalization Note** $\pi$ is `l.erase k ++ [k]` (the page's $(A, B, k', k)$ for $\pi' = (A, k, B, k')$). Non-negative processing times are an added, disclosed hypothesis: the paper's processing times are durations, and with $a_k < 0$ the jobs after $k$ would complete later in $\pi$. Completion times are prefix sums (machine starts at $0$, no idle time), via the published `MooreLateJobs.Shared.completionTime`.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §2 Sequencing Theorem, PROOF, fourth paragraph, first sentence

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace LawlerPrec.MinMax

/-- §2, proof of the Theorem, p. 544, fourth paragraph, first sentence: "No job is completed later
in π than in π′, except job k." For a sequence `π′ = l` of `J`, non-negative processing times
`a`, and `π = l.erase k ++ [k]` (the page's `π` when `l = A ++ [k] ++ B ++ [k′]`), every job
`j ≠ k` of `J` completes in `π` no later than in `π′`, and `k` completes in `π` at
`T = ∑_{j ∈ J} a_j`. -/
theorem move_last_completion_le {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (J : Finset ι)
    (ha : ∀ j ∈ J, 0 ≤ a j) (l : List ι) (hl : MooreLateJobs.Shared.IsSchedule J l) (k : ι)
    (hk : k ∈ J) :
    (∀ j ∈ J, j ≠ k →
      MooreLateJobs.Shared.completionTime a (l.erase k ++ [k]) j ≤
        MooreLateJobs.Shared.completionTime a l j) ∧
    MooreLateJobs.Shared.completionTime a (l.erase k ++ [k]) k = ∑ j ∈ J, a j := by sorry

end LawlerPrec.MinMax
