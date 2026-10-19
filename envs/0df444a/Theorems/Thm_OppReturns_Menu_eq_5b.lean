-- Prove2me | Theorems.Thm_OppReturns_Menu_eq_5b
-- name    : OppReturns.Menu.eq_5b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:42.358877+00:00
-- url     : https://prove2.me/theorems/bec756da-a04a-4de5-abe8-58aa380153b6
-- title:
--   (5b), p. 11 — the binding price is E max{u_L, r} = V_L − ∫_r^{V_L} G_L(u) du
-- statement:
--   In the model of the mission, let $u_L \sim G_L$ be an honest returner's valuation, supported on $[0, V_L]$. For every refund $r \in [0, V_L]$,
--   $$\mathbb E\max\{u_L, r\} = V_L - \int_r^{V_L} G_L(u)\,du.$$
--
--   In the uniform-refunds program the price extracts all consumer surplus from honest returners, $p = \mathbb E\max\{u_L, r\}$; this identity is the closed form (5b), $p^u = V_L - \int_{r^u}^{V_L} G_L(u)\,du$, and at $r = s$ it is the benchmark price $p^b$ of p. 10.
--
--   **Formalization Note** The standing assumptions of the mission are hypotheses, although only the support of $G_L$ is used.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 11, (5b) (and p. 10, p^b)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem eq_5b (P : Params) (hS : Standing P) :
    ∀ r ∈ Set.Icc 0 P.VL, Emax P r = P.VL - ∫ u in r..P.VL, GLf P u := by sorry

end OppReturns.Menu
