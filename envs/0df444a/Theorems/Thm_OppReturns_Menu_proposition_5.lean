-- Prove2me | Theorems.Thm_OppReturns_Menu_proposition_5
-- name    : OppReturns.Menu.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:43.149082+00:00
-- url     : https://prove2.me/theorems/77223054-86e5-4e91-a198-1c3196697426
-- title:
--   Proposition 5 (12b)–(12c), p. 16 — optimal menu pairs follow the uniform or targeted proposal
-- statement:
--   Under the standing assumptions, let $(Q^u, p^u, r^u)$ be an optimal uniform-refunds decision. Then
--
--   1. if $r^u < r^b = s$, the menu earns $\Pi^m = \Pi^u$, and some optimal menu has honest pair $(p_H^m,r_H^m)=(p^u,r^u)$ and renter fee $p_R^m-r_R^m=p^u-r^u$;
--   2. otherwise ($r^u \ge s$), the menu earns $\Pi^m = \Pi^t$, and some optimal menu has honest pair $(p_H^m,r_H^m)=(p^t,r_H^t)$ and renter fee $p_R^m-r_R^m=p^t-r_R^t$ for an optimal targeted decision.
--
--   The optimal menu either coincides with the optimal uniform-refunds proposal or reproduces the optimal targeted-refunds proposal.
--
--   **Formalization Note** The Lean statement gives an optimal menu with the pairs in (12b)–(12c) and the resulting optimal-profit equalities. It does not assert uniqueness of optimal decisions. The stock first-order condition (12a) is not formalized. As in the paper's main body (p. 11), the honest returners' constraint of program (3) is assumed to bind at every optimal uniform decision (`UniformBinds`).
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 16, Proposition 5, (12b)–(12c)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem proposition_5 (P : Params) (hS : Standing P) (hB : UniformBinds P)
    (Q p r : ℝ) (hU : IsOptU P Q p r) :
    (r < P.s → PiM P = PiU P ∧
      ∃ Qm pH rH pR rR, IsOptM P Qm pH rH pR rR ∧
        pH = p ∧ rH = r ∧ pR - rR = p - r) ∧
    (P.s ≤ r → PiM P = PiT P ∧
      ∃ Qt pt rtR rtH, IsOptT P Qt pt rtR rtH ∧
        ∃ Qm pH rH pR rR, IsOptM P Qm pH rH pR rR ∧
          pH = pt ∧ rH = rtH ∧ pR - rR = pt - rtR) := by sorry

end OppReturns.Menu
