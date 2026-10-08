-- Prove2me | Theorems.Thm_LawlerMoore_PrecDeadline_sorted_isFeasible
-- name    : LawlerMoore.PrecDeadline.sorted_isFeasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:27:55.502259+00:00
-- url     : https://prove2.me/theorems/5aeb883e-d34a-4013-80c5-2d1de2cd2d7b
-- title:
--   Section 2, proof of the Theorem — the sequence in increasing order of $\bar d_j$ observes the precedence constraints
-- statement:
--   Let $n$ jobs carry real deadlines $d_1,\dots,d_n$, let $\rho$ be a transitive precedence relation numbered so that $i\rho j$ implies $i \le j$, let $\varepsilon > 0$, and let $\bar d_j$ be the modified deadlines. Let $\sigma$ be a sequence of all $n$ jobs, each listed once, in which the modified deadlines strictly increase along the sequence. Then $\sigma$ is **consistent with the precedence constraints**:
--
--   $$
--   i\rho j,\ i \ne j \;\Longrightarrow\; i \text{ comes before } j \text{ in } \sigma .
--   $$
--
--   This is the content of the "if" part of the §2 Theorem, which the paper calls obvious: if every job is on time in the sequence ordered by $\bar d_j$, then that sequence is itself a witness that all jobs can be completed on time consistently with $\rho$.
--
--   **Formalization Note** "Consistent with the precedence constraints" is the published `LawlerPrec.MinMax.IsFeasible ρ univ σ`: $\sigma$ lists every job exactly once, and no job appears before a job that must precede it. The ordering by increasing $\bar d_j$ is stated as strict pairwise increase along the list. Jobs are `Fin n`, 0-based; $\varepsilon > 0$ is the reading of "$\varepsilon$ is a small number" needed here.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2, proof of the Theorem

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem sorted_isFeasible (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ l := by sorry

end LawlerMoore.PrecDeadline
