-- Prove2me | Theorems.Thm_OppReturns_Menu_uniform_optimum_exists
-- name    : OppReturns.Menu.uniform_optimum_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T07:59:03.859403+00:00
-- url     : https://prove2.me/theorems/a1c75eb4-e4cf-499b-8e2c-8dd8dc579c5a
-- title:
--   Program (3), pp. 10–11 — the uniform-refunds program has an optimal decision (Q^u, p^u, r^u)
-- statement:
--   In the model of the mission, a fraction $X$ of customers are renters with short-term valuation $u_S \sim G_S$ on $[0,V_S]$ and the rest are honest returners with valuation $u_L \sim G_L$ on $[0,V_L]$; demand $D$ has cdf $F$, the unit cost is $c$ and the salvage value is $s<c$. The uniform-refunds program (3) chooses a stock $Q \ge 0$, a price $p$ and a refund $r$ with $0 \le r \le p$ and $\mathbb E\max\{u_L,r\}-p \ge 0$ to maximize
--
--   $$\Pi^u(Q,p,r) = M^u(p,r)\,\mathbb E\min\Bigl\{\frac{Q}{N(p,r)},\,D\Bigr\} - (c-s)\,Q,$$
--
--   where $N(p,r) = 1 - X G_S(p-r)$ and $M^u(p,r) = (p-r)\bigl(1-XG_S(p-r)\bigr) + (r-s)(1-X)\bigl(1-G_L(r)\bigr)$.
--
--   Under the standing assumptions of the mission, program (3) has an optimal decision: there is a feasible $(Q^u,p^u,r^u)$ with
--
--   $$\Pi^u(Q,p,r) \le \Pi^u(Q^u,p^u,r^u) \quad \text{for every feasible } (Q,p,r).$$
--
--   The paper works throughout with the optimal uniform decisions $(Q^u,p^u,r^u)$ (Lemma 1, Propositions 4–6); this statement records that they exist, which is the existence part of Proposition 6.
--
--   **Formalization Note** As in the mission's model definition, the cap $p-r \le V_S$ of (3) is not imposed. Uniqueness is not claimed.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), pp. 10–11, program (3) and its optimal decisions (Q^u, p^u, r^u) used in Lemma 1 and Propositions 4–6

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem uniform_optimum_exists (P : Params) (hS : Standing P) :
    ∃ Q p r, IsOptU P Q p r := by sorry

end OppReturns.Menu
