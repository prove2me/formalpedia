-- Prove2me | Theorems.Thm_N25_Endgame_frobenius_fixedPlaces_card_eq_degree_sum25
-- name    : N25.Endgame.frobenius_fixedPlaces_card_eq_degree_sum25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:21:23.038768+00:00
-- url     : https://prove2.me/theorems/92b4a2c3-ad3b-4996-92a8-a14cb46f24e4
-- title:
--   Fixed places of Frobenius are counted by closed-place degrees
-- statement:
--   Let $p$ be prime, let $K$ be an algebraically closed field of characteristic $p$, and let $F_p$ be the prime-field level-$25$ function field. For $n>0$, let $\Phi_p$ be the q-expansion Frobenius action on places after extending constants to $K$. Then $$|\mathrm{Fix}(\Phi_p^n)|=\sum_{d\mid n}d\,|\{v\in\mathrm{Place}_{𝔽_p}(F_p):\deg v=d\}|.$$ This is the bridge from geometric Frobenius fixed points to the closed-place data entering the zeta function. Formalization note: the primality and algebraic-closedness assumptions install the required Frobenius and constant-field structures.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_FiniteBaseFunctionFields
import Definitions.Def_N25_CanonicalModularDictionaryGoodCharacteristic
import Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitBinaryFieldSemantics
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Definitions.Def_N25_ExplicitF16Field
import Definitions.Def_N25_NormalizedPointPredicates
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs

open N25
open N25.Endgame
open MazurProof.RationalPointsN25QuotientWeilThree

theorem N25.Endgame.frobenius_fixedPlaces_card_eq_degree_sum25
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (hn : 0 < n) :
    Nat.card (Function.fixedPoints ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n])) =
      ∑ d ∈ Nat.divisors n, d *
        Nat.card {v : AlgebraicCurve.Place (ZMod p) (FBase (ZMod p)) | v.deg = d} := by sorry
