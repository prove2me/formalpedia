-- Prove2me | Theorems.Thm_JuschenkoMonod_log_one_add_two_sided_bound
-- name    : JuschenkoMonod.log_one_add_two_sided_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:21:18.828128+00:00
-- url     : https://prove2.me/theorems/4763f0e2-051e-4911-98c9-f0e781437acc
-- title:
--   (2.ii) — z − Cz² ≤ log(1 + z) ≤ z for z ≥ −1/2, with C = 4 log 2 − 2 > 0
-- statement:
--   Let $C = 4\log 2 - 2$. Then $C > 0$, and every real $z \ge -\frac12$ satisfies $z - Cz^2 \le \log(1 + z) \le z$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 778, the inequality (2.ii)

import Mathlib

namespace JuschenkoMonod

theorem log_one_add_two_sided_bound :
    0 < 4 * Real.log 2 - 2 ∧ ∀ z : ℝ, -1 / 2 ≤ z →
      z - (4 * Real.log 2 - 2) * z ^ 2 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ z := by
  sorry

end JuschenkoMonod
