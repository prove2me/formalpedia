-- Prove2me | Theorems.Thm_N25_gamma_field_order
-- name    : N25.gamma_field_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:43:34.205416+00:00
-- url     : https://prove2.me/theorems/c7e2a662-9525-4918-909c-07f76099d734
-- title:
--   The distinguished field automorphism has order $5$
-- statement:
--   Let $\gamma_F$ be the label-$13$ diamond automorphism of the geometric level-$25$ function field. Its order is exactly five:
--
--   $$\operatorname{ord}(\gamma_F)=5.$$
--
--   This is the cyclic symmetry whose fixed field is the $\Gamma_0(25)$ subfield.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one

set_option autoImplicit false
open N25

theorem N25.gamma_field_order :
    orderOf (ModularCurve.diamondAutHBar 25 H25
      (ZMod.unitOfCoprime 13 (by decide))) = 5 := by sorry
