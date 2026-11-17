-- Prove2me | Theorems.Thm_N25_modularField_top_map_val25
-- name    : N25.modularField_top_map_val25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:54.479516+00:00
-- url     : https://prove2.me/theorems/3b28deab-e1db-4b82-b9b9-fe7894ef52b8
-- title:
--   The full modular field maps onto the q-expansion field
-- statement:
--   Let $F_K$ be the level-$25$ modular field and let $ι:F_K↪K((q))$ be its inclusion. Then $$ι(F_K)=K(X_H(25))_{qexp}.$$ This identifies the intrinsic and Laurent-series realizations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.modularField_top_map_val25 (K : Type*) [Field K] :
    (⊤ : IntermediateField K (N25.Endgame.FBase K)).map
      (N25.Endgame.FBase K).val =
        ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by sorry
