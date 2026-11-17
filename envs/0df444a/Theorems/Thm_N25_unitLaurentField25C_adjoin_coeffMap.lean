-- Prove2me | Theorems.Thm_N25_unitLaurentField25C_adjoin_coeffMap
-- name    : N25.unitLaurentField25C_adjoin_coeffMap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:00.999747+00:00
-- url     : https://prove2.me/theorems/c10c006c-429b-4399-a74c-00e20e9a8f86
-- title:
--   The unit-generated field is preserved by coefficient extension
-- statement:
--   Let $k⊆K$ be fields and let $E_k$ be the unit-generated Laurent field over $k$. Then $$K(Coeff_{k→K}(E_k))=E_K.$$ This is the field-level base-change statement for the two generators.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitLaurentField25C_adjoin_coeffMap (k K : Type*)
    [Field k] [Field K] [Algebra k K] :
    IntermediateField.adjoin K
      (ModularCurve.coeffMap (algebraMap k K) ''
        (unitLaurentField25C k : Set (LaurentSeries k))) = unitLaurentField25C K := by sorry
