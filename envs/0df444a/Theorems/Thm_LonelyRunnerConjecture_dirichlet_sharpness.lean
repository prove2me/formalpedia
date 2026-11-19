-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_dirichlet_sharpness
-- name    : LonelyRunnerConjecture.dirichlet_sharpness
-- status  : Proved
-- author  : @LG
-- created : 2026-11-17T01:11:39.282338+00:00
-- url     : https://prove2.me/theorems/00de48d3-c192-4b2a-a2b9-cc2a61594874
-- title:
--   Dirichlet sharpness of the $1/(k+1)$ threshold
-- statement:
--   For every integer $k\ge1$ and every real time $t$, some speed $v\in\{1,\dots,k\}$ satisfies $\|tv\|\le\frac{1}{k+1}$. This is Dirichlet's approximation theorem; it shows the conjectured threshold $\frac{1}{k+1}$ cannot be increased, since the speed set $\{1,\dots,k\}$ never has all runners strictly farther than $\frac{1}{k+1}$ from the start.
--
--   **Formalization Note** The set $\{1,\dots,k\}$ is `Finset.Icc 1 k`; the hypothesis $k\ge1$ excludes the empty range.
-- source:
--   R. D. Malikiosis, F. Santos, M. Schymura, Linearly-exponential checking is enough for the LRC, https://arxiv.org/abs/2411.06903, §1.1 (Dirichlet's approximation theorem); Tao §1, eq. (1.1).

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem dirichlet_sharpness (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ∃ v ∈ Finset.Icc 1 k, distToNearestInt (t * (v : ℝ)) ≤ (1 : ℝ) / (k + 1 : ℝ) := by sorry

end LonelyRunnerConjecture
