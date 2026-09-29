-- Prove2me | Theorems.Thm_MooreLateJobs_NumLate_moore_terminates
-- name    : MooreLateJobs.NumLate.moore_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:10:52.012453+00:00
-- url     : https://prove2.me/theorems/bdf2cae1-cb6e-4233-afee-b84044aa7fc7
-- title:
--   p. 108 — Moore's algorithm terminates
-- statement:
--   Let $J$ be a finite set of jobs with $t_j\ge0$ and $t_j\le D_j$, and let $l_0$ be a schedule of $J$ in shortest-processing-time order. There is no infinite sequence of states
--   $$
--   (l_0,\emptyset)=s_0\to s_1\to s_2\to\cdots
--   $$
--   in which each $s_{n+1}$ is obtained from $s_n$ by a pass of Steps 2–3 of Moore's algorithm.
--
--   **Formalization Note** Every tie-breaking choice is covered: the statement rules out an infinite run for all choices. $t_j\ge0$ is added.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 108, paragraph after the proof of case 3) ("This process continues ...")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_MooreStep

namespace MooreLateJobs.NumLate

theorem moore_terminates {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (l₀ : List ι) (hl₀ : Shared.IsSchedule J l₀) (hspt : l₀.Pairwise (fun a b => t a ≤ t b)) :
    ¬ ∃ f : ℕ → List ι × List ι, f 0 = (l₀, []) ∧ ∀ n, MooreStep t D (f n) (f (n + 1)) := by sorry

end MooreLateJobs.NumLate
