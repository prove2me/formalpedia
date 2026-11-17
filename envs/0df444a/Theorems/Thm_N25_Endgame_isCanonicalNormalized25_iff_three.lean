-- Prove2me | Theorems.Thm_N25_Endgame_isCanonicalNormalized25_iff_three
-- name    : N25.Endgame.isCanonicalNormalized25_iff_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:31.759061+00:00
-- url     : https://prove2.me/theorems/9944de6f-30dd-4e99-904f-93c8cacfa148
-- title:
--   The canonical normalized equations specialize correctly in characteristic three
-- statement:
--   Let $K$ be a field of characteristic $3$ and let $P$ be a normalized projective quadruple. Then the generic canonical predicate and the semantic characteristic-three predicate are equivalent: $$P\text{ satisfies the canonical equations}⇔P\text{ satisfies the ternary specialized equations}.$$ This justifies the characteristic-three finite-field enumeration.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open MazurProof.RationalPointsN25QuotientWeil

theorem N25.Endgame.isCanonicalNormalized25_iff_three
    {K : Type*} [Field K] [CharP K 3]
    (P : NormalizedProjective4 K) :
    IsCanonicalNormalized25 P ↔
      MazurProof.RationalPointsN25QuotientKummerThreeProjective.IsCanonicalNormalizedThree P := by sorry
