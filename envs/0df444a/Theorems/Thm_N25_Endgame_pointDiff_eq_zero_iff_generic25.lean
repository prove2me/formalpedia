-- Prove2me | Theorems.Thm_N25_Endgame_pointDiff_eq_zero_iff_generic25
-- name    : N25.Endgame.pointDiff_eq_zero_iff_generic25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:43.700322+00:00
-- url     : https://prove2.me/theorems/b08a9589-9097-48ed-b3d4-f4e11e7b2114
-- title:
--   A degree-one point difference vanishes exactly when the places coincide
-- statement:
--   Let $P$ and $Q$ be degree-one places of the geometric level-$25$ function field, and let $[P-Q]$ denote their degree-zero divisor class. Then
--
--   $$[P-Q]=0\quad\iff\quad P=Q.$$
--
--   This converts equality of cusp divisor classes into equality of the underlying geometric places.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_PointDifference
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.pointDiff_eq_zero_iff_generic25
    (P Q : GPlace) (hP : P.deg = 1) (hQ : Q.deg = 1) :
    pointDiff P Q (hP.trans hQ.symm) = 0 ↔ P = Q := by sorry
