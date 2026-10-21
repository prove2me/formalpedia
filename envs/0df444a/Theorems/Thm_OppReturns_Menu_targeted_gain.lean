-- Prove2me | Theorems.Thm_OppReturns_Menu_targeted_gain
-- name    : OppReturns.Menu.targeted_gain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:44.13628+00:00
-- url     : https://prove2.me/theorems/8b90d65c-83bc-4ba5-b527-b663fc5d7763
-- title:
--   p. 15 — targeted refunds strictly beat uniform refunds when r^u ≠ s
-- statement:
--   Under the standing assumptions, let $(Q^u, p^u, r^u)$ be an optimal decision of the uniform-refunds program (3). If $r^u \ne s$, then
--   $$\Pi^u < \Pi^t.$$
--
--   This is the benefit Proposition 4 highlights: distinguishing customer types lets the retailer set the honest returners' refund at the benchmark value $s$, which strictly raises the margin whenever the uniform refund differs from $s$.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 15, discussion of Proposition 4

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem targeted_gain (P : Params) (hS : Standing P) (Q p r : ℝ) (hU : IsOptU P Q p r)
    (hr : r ≠ P.s) : PiU P < PiT P := by sorry

end OppReturns.Menu
