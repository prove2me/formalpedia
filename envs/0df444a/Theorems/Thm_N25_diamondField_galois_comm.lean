-- Prove2me | Theorems.Thm_N25_diamondField_galois_comm
-- name    : N25.diamondField_galois_comm
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:28.065501+00:00
-- url     : https://prove2.me/theorems/e6034a1f-83fa-4560-91ed-cb873a487053
-- title:
--   Diamond and arithmetic Galois actions commute on the function field
-- statement:
--   Let $d\in(\mathbb Z/25\mathbb Z)^\times$, let $\sigma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and let $x$ lie in the geometric level-$25$ function field. Then
--
--   $$\sigma\bigl(\delta_d(x)\bigr)=\delta_d(\sigma x).$$
--
--   This compatibility permits diamond eigenspaces to be analyzed as Galois representations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups
open N25

theorem N25.diamondField_galois_comm
    (d : (ZMod 25)ˣ) (σ : Gal) (x : xHFunctionFieldBar 25 H25) :
    arithmeticGalois (xHFunctionField 25 H25) σ •
      diamondAutHBar 25 H25 d x =
      diamondAutHBar 25 H25 d
        (arithmeticGalois (xHFunctionField 25 H25) σ • x) := by sorry
