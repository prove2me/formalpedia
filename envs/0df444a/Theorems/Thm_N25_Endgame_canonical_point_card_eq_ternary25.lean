-- Prove2me | Theorems.Thm_N25_Endgame_canonical_point_card_eq_ternary25
-- name    : N25.Endgame.canonical_point_card_eq_ternary25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:12:51.018201+00:00
-- url     : https://prove2.me/theorems/2b4614d3-87e6-4bef-924f-c067342f886e
-- title:
--   Canonical points in characteristic three equal the normalized ternary solutions
-- statement:
--   Let $K$ be a field of characteristic $3$. Let $C(K)$ be the canonical normalized projective point set, and let $C_3(K)$ be the normalized projective quadruples satisfying the characteristic-three semantic equations. Then $$|C(K)|=|C_3(K)|.$$ This identifies the scheme-level point set with the executable ternary model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open N25

theorem N25.Endgame.canonical_point_card_eq_ternary25
    (K : Type*) [Field K] [CharP K 3] :
    Nat.card (CanonicalPoint25 K) =
      Nat.card {P : MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K //
        MazurProof.RationalPointsN25QuotientKummerThreeProjective.IsCanonicalNormalizedThree P} := by sorry
