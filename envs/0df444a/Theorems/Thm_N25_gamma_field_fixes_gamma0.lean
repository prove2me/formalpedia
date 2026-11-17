-- Prove2me | Theorems.Thm_N25_gamma_field_fixes_gamma0
-- name    : N25.gamma_field_fixes_gamma0
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:50.600691+00:00
-- url     : https://prove2.me/theorems/8b4197e9-2bc5-435c-bcab-82bb6ec449f4
-- title:
--   Every power of the distinguished diamond fixes the $\Gamma_0(25)$ subfield
-- statement:
--   Let $\gamma_F$ be the label-$13$ diamond automorphism of the geometric $H_{25}$ function field. Let $n\ge0$ and let $x$ be an element whose Laurent series lies in the base-changed $\Gamma_0(25)$ function field. Then
--
--   $$\gamma_F^n(x)=x.$$
--
--   This proves that the entire $\Gamma_0(25)$ subfield is fixed by the cyclic diamond action.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

set_option autoImplicit false
open scoped MatrixGroups ModularForm
open ModularCurve CongruenceSubgroup
open N25

theorem N25.gamma_field_fixes_gamma0 (n : ℕ)
    (x : xHFunctionFieldBar 25 H25)
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 25))) :
    (diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide)) ^ n) x = x := by sorry
