-- Prove2me | Theorems.Thm_MatchCongestion_Welfare_proposition_2
-- name    : MatchCongestion.Welfare.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:34.03032+00:00
-- url     : https://prove2.me/theorems/12408725-3b32-4989-8019-d96f60c561cc
-- title:
--   Proposition 2, p. 626 — for fixed m, α, r, β the consistency equations (6)–(7) have a unique solution (p, q)
-- statement:
--   Let $r>0$ and $\beta\in(0,1]$. Fix an application intensity $m\ge 0$ and a screening probability $\alpha\in[0,1]$. With $E(x) = (1-e^{-x})/x$ for $x\neq0$ and $E(0)=1$, there is exactly one pair $(p,q)\in\mathbb R^2$ satisfying the consistency conditions
--   $$q = \frac{1-e^{-mp}}{mp} = E(mp), \qquad p = \alpha\beta\,\frac{1-e^{-rm\beta q}}{rm\beta q} = \alpha\beta\,E(rm\beta q).$$
--
--   The unique pair is the mean-field steady state $(\mathcal P(m,\alpha),\mathcal Q(m,\alpha))$: the acceptance probability of an application and the availability of an applicant that the strategies $(m,\alpha)$ induce. It makes the equilibrium notion of Definition 1 well defined.
--
--   **Formalization Note.** The value $E(0)=1$ is the continuous extension of the ratio, which the page leaves undefined at $0$. The domains $m\ge0$, $\alpha\in[0,1]$ are those of §4.2. Uniqueness is asserted among all real pairs; any solution automatically lies in $[0,1]\times(0,1]$. The costs $c_a$, $c_s$ do not enter.
-- source:
--   Arnosti, Johari, Kanoria, Managing Congestion in Matching Markets, M&SOM 23(3):620–636 (2021), p. 626, Proposition 2

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

namespace MatchCongestion.Welfare

/-- Arnosti, Johari, Kanoria, *Managing Congestion in Matching Markets*, M&SOM 23(3):620–636 (2021),
p. 626, Proposition 2: for fixed `m`, `α`, `r`, `β` the consistency equations (6) and (7) have a unique
solution `(p, q)`.

**Formalization Note.** (6)–(7) are written through `E` (`E 0 = 1`). The domains `m ≥ 0`,
`α ∈ [0, 1]` are those of §4.2 (p. 626); `0 < r` and `0 < β ≤ 1` are the model's standing positivity
(p. 624). The costs `c_a`, `c_s` do not enter (6)–(7) and are unconstrained. Uniqueness is over all of
`ℝ × ℝ`; every solution automatically has `p ∈ [0, 1]`, `q ∈ (0, 1]`. -/
theorem proposition_2 (P : Params) (hr : 0 < P.r) (hβ : 0 < P.β) (hβ1 : P.β ≤ 1)
    (m α : ℝ) (hm : 0 ≤ m) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃! pq : ℝ × ℝ, IsMFSS P m α pq.1 pq.2 := by sorry

end MatchCongestion.Welfare
