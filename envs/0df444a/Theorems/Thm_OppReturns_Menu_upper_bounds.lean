-- Prove2me | Theorems.Thm_OppReturns_Menu_upper_bounds
-- name    : OppReturns.Menu.upper_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:42.339968+00:00
-- url     : https://prove2.me/theorems/2f0f5fc5-b4b4-4663-ade5-a9a145e94431
-- title:
--   p. 14 — targeted refunds bound the other proposals: the profit sets are bounded above, Π^m ≤ Π^t and Π^u ≤ Π^t
-- statement:
--   Under the standing assumptions:
--
--   1. the profits of the feasible decisions of the uniform-refunds program (3), the targeted-refunds program (9) and the menu-of-refunds program (11) form three sets of reals that are bounded above, so that the optimal profits $\Pi^u, \Pi^t, \Pi^m$ are genuine suprema;
--   2. the targeted-refunds optimum dominates the other two:
--   $$\Pi^m \le \Pi^t, \qquad \Pi^u \le \Pi^t.$$
--
--   The paper observes (p. 14) that profits obtained when the retailer can identify customer types bound every proposal it assesses; this is that bound for the targeted-refunds program (9), which is the comparison Proposition 6 uses.
--
--   **Formalization Note** The page states the bound for the type-by-type programs (7) and (8); the Lean statement is the bound by the optimum of the combined program (9), which is the quantity $\Pi^t$ of Proposition 6.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 14, after (8)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem upper_bounds (P : Params) (hS : Standing P) :
    BddAbove {π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r} ∧
    BddAbove {π | ∃ Q p rR rH, FeasT P Q p rR rH ∧ π = profitT P Q p rR rH} ∧
    BddAbove {π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR} ∧
    PiM P ≤ PiT P ∧ PiU P ≤ PiT P := by sorry

end OppReturns.Menu
