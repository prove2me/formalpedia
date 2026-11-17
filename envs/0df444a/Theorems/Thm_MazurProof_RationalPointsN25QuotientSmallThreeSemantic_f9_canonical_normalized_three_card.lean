-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f9_canonical_normalized_three_card
-- name    : MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9_canonical_normalized_three_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:46.229242+00:00
-- url     : https://prove2.me/theorems/c7835483-9919-4cbc-b723-ed014fd071f6
-- title:
--   The characteristic-three canonical curve has five points over $𝔽_9$
-- statement:
--   Let $F_9$ be the certified field with nine elements and let $C$ be the canonical characteristic-three model. Then $$|C(F_9)|=5.$$ This is the second extension-field moment in the characteristic-three zeta computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitSmallThreeSemantic

open MazurProof
open MazurProof.RationalPointsN25QuotientSmallThreeSemantic
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
universe u

theorem MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9_canonical_normalized_three_card :
    Nat.card {P : NormalizedProjective4 F9 // IsCanonicalNormalizedThree P} = 5 := by sorry
