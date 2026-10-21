-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_theorem_1
-- name    : MatchCongestion.Welfare.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:40.53393+00:00
-- url     : https://prove2.me/theorems/5af16139-f52d-4302-a9e8-f9403c76b9f3
-- title:
--   Theorem 1, p. 627 — under Assumption 1 there exists a unique mean-field equilibrium (m∗, α∗)
-- statement:
--   Let $r>0$, $0<\beta\le1$, $c_a>0$, $c_s>0$ satisfy Assumption 1, $\max(c_a,c_s)<\beta$. Then there is exactly one pair $(m^*,\alpha^*)\in\mathbb R^2$ that is a mean-field equilibrium: there is a steady state $(p,q)$ of $(m^*,\alpha^*)$, i.e.
--   $$q = E(m^*p),\qquad p = \alpha^*\beta\,E(rm^*\beta q),$$
--   with $m^* = \mathcal M(p)$ (the applicant best response (3)) and $\alpha^*\in\mathcal A(q)$ (the employer best-response correspondence (4)). Here $E(x) = (1-e^{-x})/x$ for $x\ne0$ and $E(0)=1$.
--
--   Existence and uniqueness of the equilibrium are what make the equilibrium welfare $\Pi^*_a,\Pi^*_e$ of Section 5 well defined.
--
--   **Formalization Note.** The positivity of $r,\beta,c_a,c_s$ and $\beta\le1$ are added to Assumption 1. Definition 1 is read with an existentially quantified steady state, equivalent by Proposition 2. With $E(0)=1$ the pair $(0,0)$ is not an equilibrium; under a literal $x/0=0$ reading of (6)–(7) it would be one, and uniqueness would fail.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 627, Theorem 1

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 627, Theorem 1: fix any `r, β, c_a, c_s` such that Assumption 1 holds; then there exists a unique
mean-field equilibrium `(m*, α*)`.

**Formalization Note.** `Standing` adds to Assumption 1 the positivity `0 < r`, `0 < β ≤ 1`, `0 < c_a`,
`0 < c_s` that the model presumes. `IsMFE` reads Definition 1 with an existentially quantified steady
state `(p, q)`, equivalent to the page by Proposition 2; (6)–(7) use `E 0 = 1`, which rules out the
spurious solution `(m, α) = (0, 0)` that a literal `x / 0 = 0` reading would create. -/
theorem theorem_1 (P : Params) (hP : P.Standing) :
    ∃! mα : ℝ × ℝ, IsMFE P mα.1 mα.2 := by sorry

end MatchCongestion.Welfare
