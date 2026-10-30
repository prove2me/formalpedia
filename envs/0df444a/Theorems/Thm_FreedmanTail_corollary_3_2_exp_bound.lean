-- Prove2me | Theorems.Thm_FreedmanTail_corollary_3_2_exp_bound
-- name    : FreedmanTail.corollary_3_2_exp_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:44.498246+00:00
-- url     : https://prove2.me/theorems/871f6774-7225-4434-b351-20b72009f164
-- title:
--   (3.2) Corollary: $\exp(\lambda x) \le 1 + \lambda x + x^2 e(\lambda)$ for $\lambda \ge 0$, $x \le 1$
-- statement:
--   For all real $\lambda \ge 0$ and $x \le 1$,
--   $$\exp(\lambda x) \le 1 + \lambda x + x^2 e(\lambda), \qquad e(\lambda) = e^\lambda - 1 - \lambda .$$
--   This pointwise inequality, integrated against the law of a random variable bounded above by $1$, yields the moment bound (3.5).
--
--   Differences from the source: none.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (3.2) Corollary, p. 106

import Mathlib
import Definitions.Def_FreedmanTail_eFun

namespace FreedmanTail

/-- **(3.2) Corollary: `exp(λx) ≤ 1 + λx + x² e(λ)` for `λ ≥ 0`, `x ≤ 1`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(3.2) Corollary, p. 106: "exp(λx) ≤ 1 + λx + x²e(λ) for λ ≥ 0 and x ≤ 1." -/
theorem corollary_3_2_exp_bound {l x : ℝ} (hl : 0 ≤ l) (hx : x ≤ 1) :
    Real.exp (l * x) ≤ 1 + l * x + x ^ 2 * eFun l := by sorry

end FreedmanTail
