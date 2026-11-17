-- Prove2me | Theorems.Thm_N25_Endgame_five_frobenius_fixed_places
-- name    : N25.Endgame.five_frobenius_fixed_places
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:00.625478+00:00
-- url     : https://prove2.me/theorems/1e0cc958-b93c-41c9-81c2-9ca50b72f204
-- title:
--   There are exactly five Frobenius-fixed places modulo $2$
-- statement:
--   Let $D_2$ be a level-$25$ reduction datum at $2$, and let $Fr_{D_2}$ act on places of the corresponding special function field. Then the fixed-point set is finite and has cardinality five:
--
--   $$Fix(Fr_{D_2})\text{ is finite},\qquad |Fix(Fr_{D_2})|=5.$$
--
--   This numerical bound, together with the five reduced cusps, exhausts all possible reductions of rational geometric places.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

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
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
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

open N25
open N25.Endgame

theorem N25.Endgame.five_frobenius_fixed_places (D₂ : RedDatum25 2) :
    (Function.fixedPoints (frobPlace25 D₂)).Finite ∧
      Nat.card (Function.fixedPoints (frobPlace25 D₂)) = 5 := by sorry
