-- Prove2me | Theorems.Thm_OppReturns_Menu_lemma_1
-- name    : OppReturns.Menu.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:41.849525+00:00
-- url     : https://prove2.me/theorems/f5b66f12-4859-4201-bdab-383dbf816ba1
-- title:
--   Lemma 1, p. 11 (first two claims) — 0 < dp^u(r)/dr ≤ 1 and d[p^u(r) − r]/dr < 0
-- statement:
--   Let $p^u(r) = \mathbb E\max\{u_L, r\}$ be the uniform-refunds price paired with refund $r$ (the binding constraint of program (3)). For every $r \in (0, V_L)$ the function $p^u$ is differentiable at $r$ with derivative $d$ satisfying
--   $$0 < \frac{dp^u(r)}{dr} = d \le 1, \qquad \frac{d\,[p^u(r) - r]}{dr} = d - 1 < 0.$$
--
--   So a more generous refund raises the price, but more slowly than the refund, and the rental fee $p^u(r) - r$ falls.
--
--   **Formalization Note** The page's Lemma 1 has a third claim, $\partial Q^u(r)/\partial r > 0$, which is false (the optimal stock decreases in $r$ on large ranges, e.g. $G_L = U[0,100]$, $G_S = U[0,50]$, $X = 0.2$, $s = 35$, normal demand, $r \in [53, 90]$) and is not formalized. The claims are stated on the open interval $(0, V_L)$, where $G_L$ lies strictly between $0$ and $1$.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 11, Lemma 1 (first two claims)

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem lemma_1 (P : Params) (hS : Standing P) :
    ∀ r ∈ Set.Ioo 0 P.VL, ∃ d : ℝ, HasDerivAt (Emax P) d r ∧ 0 < d ∧ d ≤ 1 ∧
      HasDerivAt (fun x => Emax P x - x) (d - 1) r ∧ d - 1 < 0 := by sorry

end OppReturns.Menu
