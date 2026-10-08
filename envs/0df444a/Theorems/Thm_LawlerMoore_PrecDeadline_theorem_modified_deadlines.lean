-- Prove2me | Theorems.Thm_LawlerMoore_PrecDeadline_theorem_modified_deadlines
-- name    : LawlerMoore.PrecDeadline.theorem_modified_deadlines
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:06.486672+00:00
-- url     : https://prove2.me/theorems/ff4bb78b-949d-403d-83e5-dadec4790b96
-- title:
--   Section 2, Theorem — all jobs can be on time under $\rho$ iff they are on time in order of increasing $\bar d_j$
-- statement:
--   Suppose $n$ jobs are to be processed by a single machine. Job $j$ requires $a_j \ge 0$ units of processing time and has a deadline $d_j \in \mathbb R$. Precedence constraints are given by a partial order $\rho$ on the jobs (reflexive, antisymmetric, transitive): if $i\rho j$ with $i \ne j$, job $i$ must precede job $j$. The jobs are numbered so that $i\rho j$ implies $i \le j$. For $j = 1,\dots,n$ let
--
--   $$
--   \bar d_j = \min\{d_k \mid j\rho k\} + j\varepsilon ,
--   $$
--
--   where $\varepsilon$ is a small positive number: $\varepsilon > 0$ and $n\varepsilon < d_l - d_k$ whenever $d_k < d_l$. A sequence lists every job exactly once; the machine starts at time $0$ and processes the jobs in that order without idle time, and $C_j(\sigma)$ denotes the completion time of job $j$ in sequence $\sigma$.
--
--   **Theorem (Lawler–Moore, §2).** Let $\sigma^*$ be the sequence obtained by ordering the jobs according to increasing values of $\bar d_j$. Then
--
--   $$
--   \Big(\exists\, \sigma \text{ consistent with } \rho:\ C_j(\sigma) \le d_j \ \ \forall j\Big) \iff C_j(\sigma^*) \le d_j \ \ \forall j .
--   $$
--
--   Each job can be completed on time, consistent with the precedence constraints, if and only if each job is on time in the single sequence $\sigma^*$, which depends only on the deadlines and on $\rho$, not on the processing times. Without precedence constraints this is Jackson's earliest-deadline rule. The feasibility question is thereby answered by evaluating one sequence.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based (the Lean job $j$ is the paper's job $j+1$; the tie-break uses $j+1$). Sequences and completion times are the published `MooreLateJobs.Shared.IsSchedule` and `completionTime` (start at time $0$, no idle time; idle time never helps meet a deadline); "consistent with the given precedence constraints" is the published `LawlerPrec.MinMax.IsFeasible`. The sequence $\sigma^*$ is quantified as any duplicate-free list of all jobs along which $\bar d_j$ strictly increases; under the hypotheses the $\bar d_j$ are pairwise distinct, so exactly one such list exists. Explicit readings: "$\varepsilon$ is a small number" as $\varepsilon > 0$ together with $n\varepsilon$ below every positive gap between deadlines; the processing times are assumed nonnegative, which the paper uses tacitly and which is necessary. As printed, the right-hand side does not itself assert that $\sigma^*$ observes $\rho$ (that is a separate milestone).
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2, Theorem

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem theorem_modified_deadlines (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (hrefl : ∀ j, ρ j j)
    (hantisymm : ∀ i j, ρ i j → ρ j i → i = j)
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    (∃ l' : List (Fin n), LawlerPrec.MinMax.IsFeasible ρ Finset.univ l' ∧
        ∀ j, MooreLateJobs.Shared.completionTime a l' j ≤ d j) ↔
      ∀ j, MooreLateJobs.Shared.completionTime a l j ≤ d j := by sorry

end LawlerMoore.PrecDeadline
