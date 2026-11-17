-- Prove2me | Theorems.Thm_N25_Endgame_xHGood_degreeOnePlace_card_eq_canonical25
-- name    : N25.Endgame.xHGood_degreeOnePlace_card_eq_canonical25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:21:41.552186+00:00
-- url     : https://prove2.me/theorems/062d8d2c-809b-49eb-b9f0-2bd9a380085c
-- title:
--   The modular and canonical models have equally many degree-one places
-- statement:
--   Let $p$ be either $2$ or $3$, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ modular function field over $K$, and let $C_K$ be the fraction field of the canonical quadric-cubic model. Then the coordinate-pinned field equivalence preserves the number of degree-one places: $$|\{v\in\mathrm{Place}_K(F_K):\deg v=1\}|=|\{v\in\mathrm{Place}_K(C_K):\deg v=1\}|.$$ This transfers explicit canonical-model point counts to the modular function field. Formalization note: the displayed domain instance certifies that the chosen canonical affine coordinate ring has a fraction field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

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
open N25
open MazurProof.RationalPointsN25QuotientWeilThree

theorem N25.Endgame.xHGood_degreeOnePlace_card_eq_canonical25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    Nat.card {P : AlgebraicCurve.Place K (FBase K) // P.deg = 1} =
      Nat.card {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} := by sorry
