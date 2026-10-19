-- Prove2me | Theorems.Thm_OppReturns_Menu_proposition_4_refund_order
-- name    : OppReturns.Menu.proposition_4_refund_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:44.63634+00:00
-- url     : https://prove2.me/theorems/4bf14b23-52d0-4c9d-a2e3-a94a5c586bd8
-- title:
--   Proposition 4, p. 15, last sentence — r^t_R ≥ s if and only if r^u ≥ s
-- statement:
--   Under the standing assumptions, let $(Q^u, p^u, r^u)$ be an optimal uniform-refunds decision (program (3)) and $(Q^t, p^t, r^t_R, r^t_H)$ an optimal targeted-refunds decision (program (9)). Then
--   $$r^t_R \ge r^b = s \iff r^u \ge r^b = s.$$
--
--   The renters' targeted refund exceeds the salvage value in exactly the scenarios where the uniform refund does; this links the targeted and uniform proposals and drives the case split of Propositions 5 and 6.
--
--   **Formalization Note** The statement holds for every pair of optimal decisions; uniqueness of the optima is not assumed. It is stated in the case the paper's main body treats (p. 11), where the honest returners' constraint of program (3) binds at every optimal uniform decision (`UniformBinds`).
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 15, Proposition 4, last sentence

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem proposition_4_refund_order (P : Params) (hS : Standing P) (hB : UniformBinds P)
    (Q p r : ℝ) (hU : IsOptU P Q p r) (Q' p' rR rH : ℝ) (hT : IsOptT P Q' p' rR rH) :
    P.s ≤ rR ↔ P.s ≤ r := by sorry

end OppReturns.Menu
