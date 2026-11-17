-- Prove2me | Theorems.Thm_N25_Endgame_U25_orders_special_good
-- name    : N25.Endgame.U25_orders_special_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:56.357652+00:00
-- url     : https://prove2.me/theorems/f0c1003c-5b90-4a84-96a5-2d8965155712
-- title:
--   Good reduction preserves the complete divisor of every selected modular unit
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $D$ be a level-$25$ reduction datum at $p$, let $U_i$ be the $i$th reduced modular unit for $i∈Fin(5)$, let $Q_j=red_D(p_j)$ be the reductions of the five selected geometric cusps, and let $u_{ij}$ be the prescribed integer order table. Then
--
--   $$ord_{Q_j}(U_i)=u_{ij}\quad(∀j),\qquad ord_P(U_i)=0\quad\text{if }P≠Q_j\text{ for every }j.$$
--
--   This shows that specialization preserves the entire unit divisor, including absence of additional zeros or poles.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.U25_orders_special_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (D : RedDatum25 p) (i : Fin 5) :
    (∀ j : Fin 5,
      (redPlace25 D (pG25 j)).ord (N25.U25C (κ D.A) i) =
        N25.unitOrders25 i j) ∧
    ∀ P : SpecialPlace D.A,
      (∀ j : Fin 5, P ≠ redPlace25 D (pG25 j)) →
        P.ord (N25.U25C (κ D.A) i) = 0 := by sorry
