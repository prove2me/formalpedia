-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_theorem_2_root_13
-- name    : MatchCongestion.Welfare.theorem_2_root_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:36.072619+00:00
-- url     : https://prove2.me/theorems/bc975198-4edd-4b45-8f2c-44db5c3e2e35
-- title:
--   Theorem 2 (13) part, p. 628 — a unique p̂ > c_a solves r(1 − c_a/p̂) = 1 − e^{−(rβ/p̂)(1 − c_a/p̂)}
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ with $\max(c_a,c_s)<\beta$ (Assumption 1). There is exactly one $\hat p > c_a$ such that
--   $$r\Bigl(1-\frac{c_a}{\hat p}\Bigr) = 1 - e^{-\frac{r\beta}{\hat p}\left(1-\frac{c_a}{\hat p}\right)}. \tag{13}$$
--
--   The root $\hat p$ is the acceptance probability that arises when every employer screens and applicants best respond; it is one of the two candidates for the equilibrium acceptance probability in Theorem 2.
--
--   **Formalization Note.** $p=c_a$ also solves (13); the strict inequality $\hat p>c_a$ excludes it, as on the page. The positivity of $r,\beta,c_a,c_s$ and $\beta\le1$ are added to Assumption 1.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 628, Theorem 2, equation (13)

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 628, Theorem 2, first sentence, equation (13): there is a unique `p̂ > c_a` with
`r (1 - c_a/p̂) = 1 - e^{-(rβ/p̂)(1 - c_a/p̂)}`.

**Formalization Note.** `p = c_a` also solves (13); the strict inequality `c_a < p` excludes it, as on the
page. `Standing` is Assumption 1 plus the disclosed positivity `0 < r`, `0 < β ≤ 1`, `0 < c_a`, `0 < c_s`. -/
theorem theorem_2_root_13 (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq13 P p := by sorry

end MatchCongestion.Welfare
