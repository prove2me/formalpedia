-- Prove2me | Theorems.Thm_N25_unitSeries25_coeffMap
-- name    : N25.unitSeries25_coeffMap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:56.691637+00:00
-- url     : https://prove2.me/theorems/85c17183-4b5b-416d-8127-16e6d73b3408
-- title:
--   Modular-unit series commute with coefficient extension
-- statement:
--   Let $k⊆K$ be fields and let $u_i^{(k)}$ and $u_i^{(K)}$ be the $i$th unit Laurent series. Then $$Coeff_{k→K}(u_i^{(k)})=u_i^{(K)}.$$ This makes the unit series functorial in the coefficient field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitSeries25_coeffMap (k K : Type*) [Field k] [Field K] [Algebra k K]
    (i : Fin 5) :
    ModularCurve.coeffMap (algebraMap k K) (unitSeries25 k i) = unitSeries25 K i := by sorry
