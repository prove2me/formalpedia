-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_endnote_12_eq16
-- name    : MatchCongestion.Welfare.endnote_12_eq16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:35.943313+00:00
-- url     : https://prove2.me/theorems/14d86b52-1816-422b-a509-1d16599fb19c
-- title:
--   Endnote 12 (16), p. 635 — consistency (6)–(7) and the best response (3) applied to (11) give employer welfare (16)
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ with $\max(c_a,c_s)<\beta$, and write $c'_s=c_s/\beta$. Let $(p,q)$ be a steady state of $(m,\alpha)$, i.e. $q=E(mp)$ and $p=\alpha\beta E(rm\beta q)$, suppose $m=\mathcal M(p)$ is the applicant best response and $p>c_a$. Then the employer payoff (5) equals
--   $$W_e(\alpha,m,q) = \alpha\bigl(1-e^{-rm\beta q}\bigr)\Bigl(1-\frac{c'_s}{q}\Bigr) = r\Bigl(1-\frac{c_a}{p}+\frac{c_s}{\beta}\log\Bigl(\frac{c_a}{p}\Bigr)\Bigr).$$
--
--   At the equilibrium this is the employer welfare formula (16) of Theorem 2.
--
--   **Formalization Note.** The employer best-response condition $\alpha\in\mathcal A(q)$ is not assumed: the identity uses only (6), (7) and (3). The positivity hypotheses are added to Assumption 1.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 635, endnote 12 (second sentence)

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 635, endnote 12, second sentence: applying the consistency conditions (6) and (7) to (11) and then the
applicant best response (3) gives employer welfare (16): if `(p, q)` is a steady state of `(m, α)`,
`m = M(p)` and `p > c_a`, then
`W_e(α, m, q) = r (1 - c_a/p + (c_s/β) log(c_a/p))`.

**Formalization Note.** The employer best-response condition `α ∈ A(q)` is not needed and not assumed.
(16) keeps the page's `c_s/β`, while `W_e` (5) is written with `c′_s = c_s/β`. -/
theorem endnote_12_eq16 (P : Params) (hP : P.Standing) (m α p q : ℝ)
    (hss : IsMFSS P m α p q) (hm : m = Mbr P p) (hp : P.ca < p) :
    We P α m q = P.r * (1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) := by sorry

end MatchCongestion.Welfare
