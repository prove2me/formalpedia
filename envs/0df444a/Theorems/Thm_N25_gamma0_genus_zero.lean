-- Prove2me | Theorems.Thm_N25_gamma0_genus_zero
-- name    : N25.gamma0_genus_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:08.306417+00:00
-- url     : https://prove2.me/theorems/355acead-5630-488c-ad07-66f2292bae25
-- title:
--   The $\Gamma_0(25)$ function field has genus zero
-- statement:
--   Let $F_0$ be the base change to $\overline{\mathbb Q}$ of the $q$-expansion function field for $\Gamma_0(25)$. Its function-field genus is
--
--   $$g(F_0)=0.$$
--
--   This supplies the rational base of the degree-five diamond cover.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open ModularCurve CongruenceSubgroup AlgebraicCurve
open N25

theorem N25.gamma0_genus_zero :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25))) = 0 := by sorry
