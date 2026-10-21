-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_endnote_12_eq15
-- name    : MatchCongestion.Welfare.endnote_12_eq15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:36.137776+00:00
-- url     : https://prove2.me/theorems/b643d0cf-e6f2-4546-9645-48f283ccbd82
-- title:
--   Endnote 12 (15), p. 635 — substituting the best response (3) into (10) gives applicant welfare (15)
-- statement:
--   Let $c_a>0$ and $p>c_a$, and let $m=\mathcal M(p) = \frac1p\log\frac{p}{c_a}$ be the applicant best response (3). The applicant payoff $W_a(m,p) = 1-e^{-mp}-c_am$ of (2) equals
--   $$W_a(\mathcal M(p),p) = 1-\frac{c_a}{p} + \frac{c_a}{p}\log\Bigl(\frac{c_a}{p}\Bigr).$$
--
--   Evaluated at the equilibrium acceptance probability $p^*$ this is the applicant welfare formula (15) of Theorem 2.
--
--   **Formalization Note.** Only $c_a>0$ is assumed; the identity is algebra in $p$ and $c_a$. $\log$ is the natural logarithm.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 635, endnote 12 (first sentence)

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 635, endnote 12, first sentence: substituting the applicant best response (3) into (10) gives
applicant welfare (15): for `p > c_a`,
`W_a(M(p), p) = 1 - c_a/p + (c_a/p) log(c_a/p)`.

**Formalization Note.** Only `0 < c_a` is assumed (not all of `Standing`); the identity is pure algebra
in `p` and does not use the other parameters. `log` is `Real.log`. -/
theorem endnote_12_eq15 (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    Wa P (Mbr P p) p = 1 - P.ca / p + P.ca / p * Real.log (P.ca / p) := by sorry

end MatchCongestion.Welfare
