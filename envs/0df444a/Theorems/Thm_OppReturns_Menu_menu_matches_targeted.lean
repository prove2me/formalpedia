-- Prove2me | Theorems.Thm_OppReturns_Menu_menu_matches_targeted
-- name    : OppReturns.Menu.menu_matches_targeted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:48.88084+00:00
-- url     : https://prove2.me/theorems/2c913a18-4d0d-4a6f-bebd-edf260c10e8c
-- title:
--   §7.1, p. 17 — if an optimal targeted decision has r^t_R ≥ s, the menu of refunds earns Π^m = Π^t
-- statement:
--   Under the standing assumptions, let $(Q^t, p^t, r^t_R, r^t_H)$ be an optimal targeted-refunds decision. If $r^t_R \ge s$, then
--   $$\Pi^m = \Pi^t.$$
--
--   When the renters' targeted refund is at least the salvage value, their rental fee is at most the honest returners' (p. 17), so a menu of two price-refund pairs can let each type self-select the pair the targeted retailer would have assigned to it, and the menu reproduces the targeted-refunds profit without identifying customers.
--
--   **Formalization Note** The page speaks of the renter's refund "exceeding" the salvage value; the statement includes the boundary $r^t_R = s$, where the same conclusion holds.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 17, §7.1, first paragraph

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem menu_matches_targeted (P : Params) (hS : Standing P)
    (Q p rR rH : ℝ) (hT : IsOptT P Q p rR rH) (hR : P.s ≤ rR) :
    PiM P = PiT P := by sorry

end OppReturns.Menu
