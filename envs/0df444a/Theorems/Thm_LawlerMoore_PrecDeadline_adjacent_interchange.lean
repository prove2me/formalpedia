-- Prove2me | Theorems.Thm_LawlerMoore_PrecDeadline_adjacent_interchange
-- name    : LawlerMoore.PrecDeadline.adjacent_interchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:27:56.519315+00:00
-- url     : https://prove2.me/theorems/a6928932-a857-4014-ae24-9c6ddbc08914
-- title:
--   Section 2, proof of the Theorem — adjacent $i, j$ with $\bar d_i > \bar d_j$ can be interchanged
-- statement:
--   Consider $n$ jobs on a single machine with processing times $a_j \ge 0$ and real deadlines $d_j$. The machine starts at time $0$ and processes the jobs of a sequence one after another without idle time, so the completion time $C_j(\sigma)$ of job $j$ in a sequence $\sigma$ is the total processing time of $j$ and the jobs before it. Let $\rho$ be a transitive precedence relation, numbered so that $i\rho j$ implies $i \le j$, and let $\bar d_j$ be the modified deadlines with $\varepsilon > 0$ and $n\varepsilon < d_l - d_k$ whenever $d_k < d_l$.
--
--   Suppose the sequence
--
--   $$
--   \sigma = (\,\sigma_1,\ i,\ j,\ \sigma_2\,)
--   $$
--
--   lists every job exactly once, is consistent with $\rho$, and completes every job on time ($C_x(\sigma) \le d_x$ for all $x$), and suppose $\bar d_i > \bar d_j$. Then the sequence $\sigma' = (\sigma_1, j, i, \sigma_2)$ obtained by interchanging $i$ and $j$ is again consistent with $\rho$ and again completes every job on time.
--
--   This is the exchange step of the §2 Theorem: a finite number of such interchanges transforms any on-time sequence consistent with $\rho$ into the sequence ordered by increasing $\bar d_j$.
--
--   **Formalization Note** Sequences are duplicate-free lists of all jobs (`MooreLateJobs.Shared.IsSchedule`) with completion times `MooreLateJobs.Shared.completionTime` (start at $0$, no idle time); consistency with $\rho$ is `LawlerPrec.MinMax.IsFeasible`. The hypothesis $a_j \ge 0$ is not stated in the paper but is used by its argument ("$j$ will remain on time since it will be earlier in the sequence") and is necessary. The paper's "$\varepsilon$ is a small number" is made explicit as above. Jobs are `Fin n`, 0-based.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2, proof of the Theorem

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem adjacent_interchange (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l₁ l₂ : List (Fin n)) (i j : Fin n)
    (hfeas : LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ i :: j :: l₂))
    (hon : ∀ x, MooreLateJobs.Shared.completionTime a (l₁ ++ i :: j :: l₂) x ≤ d x)
    (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ j :: i :: l₂) ∧
      ∀ x, MooreLateJobs.Shared.completionTime a (l₁ ++ j :: i :: l₂) x ≤ d x := by sorry

end LawlerMoore.PrecDeadline
