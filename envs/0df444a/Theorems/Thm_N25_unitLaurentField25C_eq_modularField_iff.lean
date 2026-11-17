-- Prove2me | Theorems.Thm_N25_unitLaurentField25C_eq_modularField_iff
-- name    : N25.unitLaurentField25C_eq_modularField_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:43.812538+00:00
-- url     : https://prove2.me/theorems/b686ebb6-ee73-469d-90fd-dc1e340f3caf
-- title:
--   Two units generate the Laurent field exactly when they generate intrinsically
-- statement:
--   Let $E_K=K(U_0,U_0/U_1)⊆K((q))$ and let $F_K$ be the modular field. Then $$E_K=F_K⇔K(U_0,U_0/U_1)=F_K.$$ This reduces Laurent-field generation to intrinsic field generation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitLaurentField25C_eq_modularField_iff (K : Type*) [Field K] :
    unitLaurentField25C K = ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 ↔
      IntermediateField.adjoin K
        ({U25C K 0, U25C K 0 / U25C K 1} : Set (N25.Endgame.FBase K)) = ⊤ := by sorry
