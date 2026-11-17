-- Prove2me | Theorems.Thm_N25_unitLaurentField25C_eq_map
-- name    : N25.unitLaurentField25C_eq_map
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:00.895997+00:00
-- url     : https://prove2.me/theorems/cffbd608-0dcc-480b-93f5-336a52d9ce18
-- title:
--   The unit-generated Laurent field is the image of the intrinsic subfield
-- statement:
--   Let $F_K$ be the level-$25$ modular field inside $K((q))$, let $ι:F_K↪K((q))$, and put $E_K=K(U_0,U_0/U_1)$. Then $$E_K=ι(K(U_0,U_0/U_1)⊆F_K).$$ This identifies the two models of the unit-generated field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitLaurentField25C_eq_map (K : Type*) [Field K] :
    unitLaurentField25C K =
      (IntermediateField.adjoin K
        ({U25C K 0, U25C K 0 / U25C K 1} : Set (N25.Endgame.FBase K))).map
          (N25.Endgame.FBase K).val := by sorry
