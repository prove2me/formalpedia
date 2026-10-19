-- Prove2me | Theorems.Thm_OppReturns_Menu_proposition_4_bc
-- name    : OppReturns.Menu.proposition_4_bc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:49.057575+00:00
-- url     : https://prove2.me/theorems/23cf72a3-d1da-4cca-ab01-4646d66bbe2e
-- title:
--   Proposition 4 (10b)–(10c), pp. 14–15 — an optimal targeted decision exists, and every one has p^t = p^b and r^t_H = s
-- statement:
--   Under the standing assumptions, the targeted-refunds program (9) has an optimal decision $(Q^t, p^t, r^t_R, r^t_H)$, and every optimal decision satisfies
--   $$p^t = p^b = \mathbb E\max\{u_L, s\} = V_L - \int_s^{V_L} G_L(u)\,du \quad (10b), \qquad r^t_H = r^b = s \quad (10c).$$
--
--   When honest returners are identified, the retailer prices and refunds them exactly as in the benchmark without renters.
--
--   **Formalization Note** The first-order conditions (10a) and (10d) are not formalized. The price is written $\mathbb E\max\{u_L, s\}$, which equals the page's integral form by (5b).
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), pp. 14–15, Proposition 4, (10b), (10c)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem proposition_4_bc (P : Params) (hS : Standing P) :
    (∃ Q p rR rH, IsOptT P Q p rR rH) ∧
    ∀ Q p rR rH, IsOptT P Q p rR rH → p = Emax P P.s ∧ rH = P.s := by sorry

end OppReturns.Menu
