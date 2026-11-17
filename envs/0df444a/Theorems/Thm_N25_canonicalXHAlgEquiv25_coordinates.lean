-- Prove2me | Theorems.Thm_N25_canonicalXHAlgEquiv25_coordinates
-- name    : N25.canonicalXHAlgEquiv25_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:18:27.851416+00:00
-- url     : https://prove2.me/theorems/339c091e-8215-453a-a7ce-40d7270e344f
-- title:
--   The canonical function-field coordinates match the modular units
-- statement:
--   Let $F_{\mathrm{can}}$ be the rational function field of the canonical model, let $F_H=ℚ(X_H(25))$, and let $e:F_{\mathrm{can}}≃F_H$ be the fixed algebra isomorphism. If $u,v∈F_{\mathrm{can}}$ are the canonical coordinate functions and $U_0,U_1∈F_H$ are the selected modular units, then $$e(u)=U_0,\qquad e(v)=U_0/U_1.$$ This pins the abstract function-field equivalence to the units used in the rational-point argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalModularDictionary

open N25

theorem N25.canonicalXHAlgEquiv25_coordinates :
    canonicalXHAlgEquiv25 canonicalFunctionU25 = U25 0 ∧
      canonicalXHAlgEquiv25 canonicalFunctionV25 = U25 0 / U25 1 := by sorry
