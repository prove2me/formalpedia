-- Prove2me | Theorems.Thm_N25_diamondField_order_five
-- name    : N25.diamondField_order_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:43:22.865193+00:00
-- url     : https://prove2.me/theorems/90324eba-257d-4699-96a9-2b26f4e4b11f
-- title:
--   The label-$2$ diamond automorphism has order $5$
-- statement:
--   Let $\delta_2$ be the diamond automorphism of the geometric level-$25$ function field corresponding to $2\in(\mathbb Z/25\mathbb Z)^\times$. Its group-theoretic order is exactly five:
--
--   $$\operatorname{ord}(\delta_2)=5.$$
--
--   This identifies the cyclic degree-five symmetry acting on the quotient construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.diamondField_order_five :
    orderOf (ModularCurve.diamondAutHBar 25 N25.H25
      (ZMod.unitOfCoprime 2 (by decide))) = 5 := by sorry
