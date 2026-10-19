-- Prove2me | Theorems.Thm_OppReturns_Menu_proposition_6
-- name    : OppReturns.Menu.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:52.497981+00:00
-- url     : https://prove2.me/theorems/b6a36483-936a-4a54-bb01-04f249b1ce68
-- title:
--   Proposition 6 (corrected), p. 17 — Π^u ≤ Π^m ≤ Π^t; Π^t > Π^m = Π^u iff r^u < s; r^u > s ⇒ Π^t = Π^m > Π^u; r^u = s ⇒ Π^t = Π^m
-- statement:
--   Let $\Pi^u, \Pi^t, \Pi^m$ be the optimal profits of the uniform-refunds program (3), the targeted-refunds program (9) and the menu-of-refunds program (11), and let $r^b = s$ be the benchmark refund. Under the standing assumptions, and in the case where the honest returners' constraint of (3) binds at every optimal uniform decision (p. 11), an optimal uniform-refunds decision $(Q^u, p^u, r^u)$ exists, and every such decision satisfies
--
--   1. $\Pi^u \le \Pi^m \le \Pi^t$;
--   2. (a) $\Pi^t > \Pi^m = \Pi^u$ if and only if $r^u < s$;
--   3. (b) if $r^u > s$, then $\Pi^t = \Pi^m > \Pi^u$;
--   4. (c) if $r^u = s$, then $\Pi^t = \Pi^m$.
--
--   Together, (a) and (c) give
--   $$\Pi^m = \Pi^t \iff r^u \ge s:$$
--   a retailer who cannot identify renters, but offers a menu of two price-refund pairs, earns as much as one who can identify them exactly when the optimal uniform refund is at least the salvage value.
--
--   **Formalization Note** This is a corrected Proposition 6. As printed, (b) is an equivalence and (c) reads "$\Pi^t = \Pi^m = \Pi^u$ otherwise", i.e. at $r^u = s$. Both fail: with $V_L = 100$, $c = 40$, $X = 0.2$, $s = 30$, $G_L = U[0, 100]$, $G_S = U[0, 20]$ and demand $N(100, 20^2)$ (the setting of Figure 1), the optimal uniform refund is $r^u = 30 = s$ (rental fee $24.5 > V_S$, renters priced out, $\Pi^u \approx 1007.8$), while the targeted optimum has $r^t_R \approx 38.95 > s$ and $\Pi^t = \Pi^m \approx 1026.4 > \Pi^u$. So at $r^u = s$ one has $\Pi^t = \Pi^m$ but possibly $\Pi^m > \Pi^u$; clause (c) keeps only the part that holds, and (b) keeps the printed "if" direction. The existence of an optimal uniform decision is part of the conclusion, so the statement is not vacuous; uniqueness is not assumed, and every optimal uniform decision satisfies the conclusions. Program (3) keeps its constraint $\mathbb E\max\{u_L, r\} - p \ge 0$, and the statement is made in the case the paper's main body treats (p. 11): that constraint binds at every optimal uniform decision (`UniformBinds`). Without this hypothesis, a uniform program forced to bind could be beaten by a menu offering the same slack pair twice, and $\Pi^m = \Pi^u$ would fail.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 17, Proposition 6 (corrected)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem proposition_6 (P : Params) (hS : Standing P) (hB : UniformBinds P) :
    (∃ Q p r, IsOptU P Q p r) ∧
    ∀ Q p r, IsOptU P Q p r →
      PiU P ≤ PiM P ∧ PiM P ≤ PiT P ∧
      ((PiM P < PiT P ∧ PiM P = PiU P) ↔ r < P.s) ∧
      (P.s < r → PiT P = PiM P ∧ PiU P < PiM P) ∧
      (r = P.s → PiT P = PiM P) := by sorry

end OppReturns.Menu
