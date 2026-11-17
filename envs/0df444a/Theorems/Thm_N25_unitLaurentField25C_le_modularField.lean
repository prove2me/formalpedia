-- Prove2me | Theorems.Thm_N25_unitLaurentField25C_le_modularField
-- name    : N25.unitLaurentField25C_le_modularField
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:14.076204+00:00
-- url     : https://prove2.me/theorems/7eb26862-65e1-493d-9ec7-bd8c1e712e32
-- title:
--   The two-unit field lies in the modular function field
-- statement:
--   For a field $K$, let $E_K=K(U_0,U_0/U_1)⊆K((q))$. Then $$E_K⊆K(X_H(25))_{qexp}.$$ This records that both generators are modular functions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitLaurentField25C_le_modularField (K : Type*) [Field K] :
    unitLaurentField25C K ≤ ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by sorry
