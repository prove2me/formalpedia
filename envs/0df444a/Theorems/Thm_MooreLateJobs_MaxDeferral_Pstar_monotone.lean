-- Prove2me | Theorems.Thm_MooreLateJobs_MaxDeferral_Pstar_monotone
-- name    : MooreLateJobs.MaxDeferral.Pstar_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:35:55.475648+00:00
-- url     : https://prove2.me/theorems/a302b9f8-053e-49a7-becd-4f5a856c2804
-- title:
--   $P^*$ is non-decreasing for a continuous non-decreasing cost
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be continuous and non-decreasing, and let $P^*$ be its generalized inverse (times $s\ge 0$; values in $\mathbb R\cup\{+\infty\}$). Then $P^*$ is non-decreasing:
--
--   $$
--   y_1\le y_2 \implies P^*(y_1)\le P^*(y_2).
--   $$
--
--   This is the step of Moore's argument that makes the feasibility of the due-date schedule $S_D(y)$ monotone in the cost level $y$.
--
--   **Formalization Note** The paper's costs are also bounded; boundedness is not needed here and is not assumed (a stronger statement). Continuity is assumed, as in the paper; without it the claim can fail.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 109, first paragraph ("Since the P_i's are monotonically non-decreasing, the P_i*'s are monotonically non-decreasing")

import Mathlib
import Definitions.Def_MooreLateJobs_MaxDeferral_Pstar

namespace MooreLateJobs.MaxDeferral

theorem Pstar_monotone (f : ℝ → ℝ) (hcont : Continuous f) (hmono : Monotone f) :
    Monotone (Pstar f) := by sorry

end MooreLateJobs.MaxDeferral
