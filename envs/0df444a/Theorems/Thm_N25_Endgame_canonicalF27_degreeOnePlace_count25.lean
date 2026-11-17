-- Prove2me | Theorems.Thm_N25_Endgame_canonicalF27_degreeOnePlace_count25
-- name    : N25.Endgame.canonicalF27_degreeOnePlace_count25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:57.517729+00:00
-- url     : https://prove2.me/theorems/124f10d3-6123-4834-83c6-4e173f7af7f4
-- title:
--   The canonical function field has twenty degree-one places over $𝔽_{27}$
-- statement:
--   Let $K=𝔽_{27}$ be the certified field with twenty-seven elements, and let $F_K$ be the canonical level-$25$ function field. With the selected open chart a domain, $$|\{P∈\operatorname{Place}_K(F_K):\deg P=1\}|=20.$$ This is the cubic-extension count for characteristic three.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

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
open MazurProof.RationalPointsN25QuotientBinaryFieldSemantics
open MazurProof.RationalPointsN25QuotientWeilThree

theorem N25.Endgame.canonicalF27_degreeOnePlace_count25 :
    letI : IsDomain (CanonicalOpenChartRing25 F27) :=
      canonicalOpenChartRing_isDomain_good25 3 (Or.inr rfl) F27
    Nat.card {P : AlgebraicCurve.Place F27 (CanonicalFF25 F27) //
      P.deg = 1} = 20 := by sorry
