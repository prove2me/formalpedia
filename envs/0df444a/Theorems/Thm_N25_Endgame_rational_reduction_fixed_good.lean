-- Prove2me | Theorems.Thm_N25_Endgame_rational_reduction_fixed_good
-- name    : N25.Endgame.rational_reduction_fixed_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:29.867194+00:00
-- url     : https://prove2.me/theorems/242364b2-2a0a-49e4-8bc3-32fd188fd084
-- title:
--   Rational geometric places reduce to Frobenius-fixed places at $2$ and $3$
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $D$ be a level-$25$ reduction datum at $p$, and let $P$ be a degree-one geometric place fixed by arithmetic Galois. If $Fr_D$ denotes Frobenius on special-fiber places, then
--
--   $$Fr_D(red_D(P))=red_D(P).$$
--
--   This gives the uniform rational-to-Frobenius-fixed compatibility at both good primes used in the endgame.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_PointDifference
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries
import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.rational_reduction_fixed_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p)
    (P : GPlace) (hP : IsRationalGeomPlace P) :
    frobPlace25 D (redPlace25 D P) = redPlace25 D P := by sorry
