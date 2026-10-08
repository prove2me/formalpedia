-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_clause_ineq
-- name    : OptInapprox.Bal2Sat.clause_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:57.688914+00:00
-- url     : https://prove2.me/theorems/60145ca9-e05f-4a1b-8e25-62d5a97af8b5
-- title:
--   Proof of Thm 4, pp. 21–22 — 3/4 − (1/4)(1 − (2/π) arccos t) ≥ β(3/4 − t/4) for all t ∈ [−1, 1]
-- statement:
--   Let $\beta = \min_{\pi/2 \le \theta \le \pi} \frac{2 + (2/\pi)\theta}{3 - \cos\theta}$ be the constant of Theorem 3. Then for every $t \in [-1, 1]$,
--   $$
--   \tfrac34 - \tfrac14\Bigl(1 - \tfrac{2}{\pi}\arccos t\Bigr) \;\ge\; \beta\Bigl(\tfrac34 - \tfrac14\, t\Bigr).
--   $$
--
--   With $t = \cos\theta$ this says $\frac{2 + (2/\pi)\theta}{3-\cos\theta} \ge \beta$ for all $\theta \in [0,\pi]$, i.e. that the minimum defining $\beta$ is unchanged when $\rho = \cos\theta$ ranges over all of $[-1,1]$. Applied with $t = (r_iv_i)\cdot(r_jv_j)$ it is the per-clause comparison between the expected value of a rounded clause and its contribution to the semidefinite objective.
--
--   **Formalization Note** $\beta$ is defined as Theorem 3 defines it, over $\theta \in [\pi/2, \pi]$ only; the extension to $t \in [-1,1]$ (i.e. $\theta \in [0,\pi]$) is the content of this statement.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 21–22, §9, proof of Theorem 4 (last display and "the fact that it is unchanged if we let ρ range over [−1, 1]"); p. 12, Theorem 3 (β)

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting

namespace OptInapprox.Bal2Sat

/-- Per-clause inequality, proof of Theorem 4, pp. 21–22: for every `t ∈ [−1, 1]`,
`3/4 − (1/4)(1 − (2/π) arccos t) ≥ β (3/4 − (1/4) t)`, where `β` is Theorem 3's minimum over
`θ ∈ [π/2, π]`; this is "β is unchanged if we let ρ range over [−1, 1]". -/
theorem clause_ineq (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    beta * (3 / 4 - 1 / 4 * t) ≤ 3 / 4 - 1 / 4 * (1 - 2 / Real.pi * Real.arccos t) := by sorry

end OptInapprox.Bal2Sat
