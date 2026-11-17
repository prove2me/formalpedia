-- Prove2me | Theorems.Thm_N25_unitOrders25_annihilator_certificate
-- name    : N25.unitOrders25_annihilator_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:19.241895+00:00
-- url     : https://prove2.me/theorems/0ddf5f28-9aa6-4b0e-9a1f-2cc3da727535
-- title:
--   An explicit integer matrix annihilates all cusp differences by $71$
-- statement:
--   Let $m_{rk}$ be the order of the $r$th modular unit at the $k$th selected geometric cusp, and let $$C=\begin{pmatrix}0&0&0&0&0\12&1&17&26&0\1&6&31&14&0\17&31&30&25&0\26&14&25&9&0\end{pmatrix}.$$ For all $i,j,k∈ℤ/5ℤ$, $$\sum_{r=0}^{4}(C_{jr}-C_{ir})m_{rk}=71(δ_{ki}-δ_{kj}).$$ This is the explicit linear-algebra certificate that $71$ kills every difference of selected cusp classes.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitOrders

set_option autoImplicit false
open N25

theorem N25.unitOrders25_annihilator_certificate :
    let C : Fin 5 → Fin 5 → ℤ :=
      ![![0,0,0,0,0], ![12,1,17,26,0], ![1,6,31,14,0],
        ![17,31,30,25,0], ![26,14,25,9,0]]
    ∀ i j k : Fin 5,
      (∑ r : Fin 5, (C j r-C i r)*unitOrders25 r k) =
        71*((if k=i then 1 else 0)-(if k=j then 1 else 0)) := by sorry
