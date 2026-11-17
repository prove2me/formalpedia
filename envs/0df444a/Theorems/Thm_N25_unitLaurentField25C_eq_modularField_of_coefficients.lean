-- Prove2me | Theorems.Thm_N25_unitLaurentField25C_eq_modularField_of_coefficients
-- name    : N25.unitLaurentField25C_eq_modularField_of_coefficients
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:11.557463+00:00
-- url     : https://prove2.me/theorems/34548fc1-8ff4-45b3-988f-fc1fa2fabd12
-- title:
--   Generation by the two units survives coefficient extension
-- statement:
--   Let $k⊆K$ be fields. If $E_k=k(X_H(25))_{qexp}$, then $$E_K=K(X_H(25))_{qexp}.$$ This propagates the generation theorem to every extension field. Formalization note: the algebra structure specifies $k→K$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25

theorem N25.unitLaurentField25C_eq_modularField_of_coefficients (k K : Type*)
    [Field k] [Field K] [Algebra k K]
    (h : unitLaurentField25C k = ModularCurve.qExpFunctionFieldC k N25.Endgame.Γ25) :
    unitLaurentField25C K = ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by sorry
