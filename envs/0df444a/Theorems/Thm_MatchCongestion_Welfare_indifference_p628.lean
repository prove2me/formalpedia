-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_indifference_p628
-- name    : MatchCongestion.Welfare.indifference_p628
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:39.080002+00:00
-- url     : https://prove2.me/theorems/4e22a74a-0c81-4416-9cb6-bb996bcb8b89
-- title:
--   §5.1, p. 628 — at the applicant best response, employers are exactly indifferent about screening iff p solves (14)
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ with $\max(c_a,c_s)<\beta$, and write $c'_s = c_s/\beta$. Let $p>c_a$, let $m=\mathcal M(p)$ be the applicant best response (3), and let $q=E(mp)$ be the availability given by (6), with $E(x)=(1-e^{-x})/x$. Then
--   $$q = c'_s \iff 1-\frac{c_a}{p} + \frac{c_s}{\beta}\log\Bigl(\frac{c_a}{p}\Bigr) = 0 .$$
--
--   By the employer best-response correspondence (4), $q=c'_s$ is exactly the case in which every screening probability $\alpha\in[0,1]$ is optimal, i.e. employers are indifferent about whether to screen. The statement formalizes the sentence after Theorem 2 that $\bar p$ is the acceptance probability at which, when applicants respond optimally, employers are exactly indifferent.
--
--   **Formalization Note.** Indifference is read through (4); Proposition 1, which justifies (4) from the employer's sequential screening problem, is not formalized. The positivity hypotheses are added to Assumption 1.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 628, §5.1 (discussion after Theorem 2, unnumbered)

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 628, §5.1 (discussion after Theorem 2, unnumbered): `p̄` is the acceptance probability at which, when
applicants respond optimally, employers are exactly indifferent about whether to screen. Formally, for
`p > c_a`, with `m = M(p)` and `q` given by (6), `q = c′_s` (the indifference case of (4)) holds exactly
when `p` solves (14).

**Formalization Note.** "Exactly indifferent" is read through the correspondence (4): `A(q) = [0, 1]`
iff `q = c′_s`. Proposition 1 (the employer's dynamic problem, Online Appendix C) is not formalized. -/
theorem indifference_p628 (P : Params) (hP : P.Standing) (p : ℝ) (hp : P.ca < p) :
    E (Mbr P p * p) = csp P ↔ Eq14 P p := by sorry

end MatchCongestion.Welfare
