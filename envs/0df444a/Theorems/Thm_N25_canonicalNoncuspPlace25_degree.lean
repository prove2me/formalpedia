-- Prove2me | Theorems.Thm_N25_canonicalNoncuspPlace25_degree
-- name    : N25.canonicalNoncuspPlace25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:33.171234+00:00
-- url     : https://prove2.me/theorems/a65a2164-fdca-47d5-9cf0-8f8ffe6bba8c
-- title:
--   Every rational noncuspidal canonical point gives a degree-one place
-- statement:
--   Let $(x:y:z:w)∈ℙ^3(ℚ)$ be represented by a nonzero quadruple satisfying the canonical equations $Q(x,y,z,w)=0$ and $C(x,y,z,w)=0$, and assume it is not one of the designated canonical cusps. Let $P_{x,y,z,w}$ be the associated place of the canonical function field. Then $$\deg(P_{x,y,z,w})=1.$$ This turns a rational noncusp on the projective model into a rational function-field place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalNoncuspPlace
import Definitions.Def_N25_UnitPlanePointPlace

open N25

theorem N25.canonicalNoncuspPlace25_degree (x y z w : ℚ)
    (hnz : MazurProof.RationalPointsN25CanonicalPoints.NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ MazurProof.RationalPointsN25CanonicalPoints.IsCanonicalCusp25 x y z w) :
    (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).deg = 1 := by sorry
