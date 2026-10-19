-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_endnote_13
-- name    : MatchCongestion.Welfare.endnote_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:38.425929+00:00
-- url     : https://prove2.me/theorems/971fcd53-11ca-49bc-9f4b-d49cffa4972d
-- title:
--   Endnote 13, p. 635 — when all employers screen, consistency (7) at the applicant best response is equation (13)
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ with $\max(c_a,c_s)<\beta$. Let $p>c_a$, let $m=\mathcal M(p)=\frac1p\log\frac p{c_a}$ be the applicant best response (3), and let $q = E(mp)$ be the availability given by the consistency condition (6), where $E(x)=(1-e^{-x})/x$ ($E(0)=1$). Then:
--
--   1. an applicant matches with probability $1-e^{-mp} = 1-\dfrac{c_a}{p}$;
--   2. an always-screening employer matches with probability
--   $$1-e^{-rm\beta q} = 1 - e^{-\frac{r\beta}{p}\left(1-\frac{c_a}{p}\right)},$$
--   the right side of (13);
--   3. the consistency condition (7) with $\alpha=1$, $p=\beta\,E(rm\beta q)$, holds if and only if $p$ solves (13).
--
--   This is the interpretation of (13) given in the endnote: the left side of (13) is the mass of matched applicants and the right side is the probability that an always-screening employer hires. Part 3 identifies the equilibrium acceptance probability with $\hat p$ when every employer screens.
--
--   **Formalization Note.** Part 3 is the precise form in which the endnote's identification is used; parts 1–2 are its literal content. The positivity hypotheses are added to Assumption 1.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 635, endnote 13

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 635, endnote 13 (interpretation of (13)): for an acceptance probability `p > c_a`, the applicant best
response `m = M(p)` of (3) matches with probability `1 - e^{-mp} = 1 - c_a/p` (the left side of (13) over
`r`); with `q` given by (6), an always-screening employer matches with probability
`1 - e^{-rmβq}`, which equals the right side of (13); consequently the consistency condition (7) with
`α = 1` holds exactly when `p` solves (13).

**Formalization Note.** `q = E (m p)` is (6) through `E`; part (c) is the form in which the endnote is
used to identify `p*` with `p̂` when every employer screens. -/
theorem endnote_13 (P : Params) (hP : P.Standing) (p : ℝ) (hp : P.ca < p) :
    (1 - Real.exp (-(Mbr P p * p)) = 1 - P.ca / p) ∧
    (1 - Real.exp (-(P.r * Mbr P p * P.β * E (Mbr P p * p))) =
      1 - Real.exp (-(P.r * P.β / p) * (1 - P.ca / p))) ∧
    (p = 1 * P.β * E (P.r * Mbr P p * P.β * E (Mbr P p * p)) ↔ Eq13 P p) := by sorry

end MatchCongestion.Welfare
