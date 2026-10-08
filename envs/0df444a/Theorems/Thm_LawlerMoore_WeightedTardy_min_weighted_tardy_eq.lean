-- Prove2me | Theorems.Thm_LawlerMoore_WeightedTardy_min_weighted_tardy_eq
-- name    : LawlerMoore.WeightedTardy.min_weighted_tardy_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:31.857581+00:00
-- url     : https://prove2.me/theorems/cd47d5b1-7c16-45cf-894b-7b825f1e234c
-- title:
--   Sections 5–6 and Eq. (3) — the minimum weighted number of tardy jobs is Σ p_j − f(n, d_n)
-- statement:
--   Let $n \ge 1$ jobs be processed one at a time by a single machine. Job $j$ has a nonnegative integer processing time $a'_j$, a nonnegative integer deadline $d_j$ and a penalty $p_j \ge 0$, paid if the job completes after its deadline; the jobs are numbered so that
--   $$
--   d_1 \le d_2 \le \cdots \le d_n .
--   $$
--   Let $f$ be defined by Equation (3), $f(j,t) = \max\{f(j, t-1), f(j-1, t), p_j + f(j-1, t-a'_j)\}$ for $t \le d_j$ and $f(j, t) = f(j, d_j)$ for $t > d_j$, with $f(0, t) = 0$ for $t \ge 0$ and $f(j, t) = -\infty$ for $t < 0$. Then $f(n, d_n)$ is a real number and
--   $$
--   \min_{\sigma} \sum_{j \text{ tardy in } \sigma} p_j \;=\; \sum_{j=1}^n p_j - f(n, d_n),
--   $$
--   the minimum being taken over all sequences $\sigma$ of the jobs (and attained).
--
--   This is the paper's solution of the problem of minimizing the weighted number of tardy jobs on one machine: order the jobs by deadline and evaluate Equation (3).
--
--   **Formalization Note** The paper says "the problem is solved by" (1), equivalently (3), without naming the argument at which $f$ is read; the evaluation point $(n, d_n)$ is made explicit ($f(n, t) = f(n, d_n)$ for all $t \ge d_n$ by the cap). $n \ge 1$ is assumed only so that $d_n$ exists. Processing times and deadlines are natural numbers (as the unit steps of (3) require), penalties are real and nonnegative, and the deadline numbering is `Monotone d` on the job index. Sequences are schedules in the published list model (`IsSchedule`, `completionTime`, `lateSet`); "minimum" is `IsLeast` over the set of values of all schedules. The base cases of (3) are those of (1) with $-\infty$ for a maximum.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), pp. 79–80, Sections 5–6 and Eq. (3)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_eq3

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared

/-- §§5–6 and Eq. (3) (pp. 79–80): with the jobs numbered by deadline (`d` monotone) and
penalties `p j ≥ 0`, the value `f(n, d_n)` of Equation (3) is finite, `f(n, d_n) = V`, and the
minimum over all sequences of the weighted number of tardy jobs is `∑_j p_j - V`. -/
theorem min_weighted_tardy_eq {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by sorry

end LawlerMoore.WeightedTardy
