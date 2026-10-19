-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_theorem_2_root_14
-- name    : MatchCongestion.Welfare.theorem_2_root_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:42.186403+00:00
-- url     : https://prove2.me/theorems/77633eb0-60a9-4af9-bb57-09c1359c83bc
-- title:
--   Theorem 2 (14) part, p. 628 — a unique p̄ > c_a solves 1 − c_a/p̄ + (c_s/β) log(c_a/p̄) = 0
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ with $\max(c_a,c_s)<\beta$ (Assumption 1). There is exactly one $\bar p > c_a$ such that
--   $$1-\frac{c_a}{\bar p} + \frac{c_s}{\beta}\log\Bigl(\frac{c_a}{\bar p}\Bigr) = 0. \tag{14}$$
--
--   The root $\bar p$ is the acceptance probability at which employers are indifferent about screening when applicants best respond; it is the second candidate for the equilibrium acceptance probability in Theorem 2.
--
--   **Formalization Note.** $p=c_a$ also solves (14); the strict inequality $\bar p>c_a$ excludes it, as on the page. $\log$ is the natural logarithm. The positivity of $r,\beta,c_a,c_s$ and $\beta\le1$ are added to Assumption 1.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 628, Theorem 2, equation (14)

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 628, Theorem 2, first sentence, equation (14): there is a unique `p̄ > c_a` with
`1 - c_a/p̄ + (c_s/β) log(c_a/p̄) = 0`.

**Formalization Note.** `p = c_a` also solves (14); the strict inequality `c_a < p` excludes it, as on the
page. `log` is `Real.log`. `Standing` is Assumption 1 plus the disclosed positivity. -/
theorem theorem_2_root_14 (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq14 P p := by sorry

end MatchCongestion.Welfare
