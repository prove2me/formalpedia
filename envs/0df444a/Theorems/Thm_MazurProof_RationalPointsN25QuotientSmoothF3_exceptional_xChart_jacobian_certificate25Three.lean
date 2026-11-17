-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_exceptional_xChart_jacobian_certificate25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.exceptional_xChart_jacobian_certificate25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:44.365995+00:00
-- url     : https://prove2.me/theorems/1eb8132f-e1df-475b-bff1-bcd1af185207
-- title:
--   An explicit Bézout identity resolves the exceptional characteristic-three $x$-chart branch
-- statement:
--   Let $K$ be a field of characteristic $3$ and let $y,w∈K$. Then $$(w^2-w)(y^2+y-1)+(-wy+w+1)(y+w-w^2)+(w^2+wy+1)(1-y)(1+w)=1.$$ This unit-ideal certificate excludes singularities on the exceptional branch left by the residual calculation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF3
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

theorem MazurProof.RationalPointsN25QuotientSmoothF3.exceptional_xChart_jacobian_certificate25Three
    {K : Type*} [Field K] [CharP K 3] (y w : K) :
    (w ^ 2 - w) * (y ^ 2 + y - 1) +
      (-w * y + w + 1) * (y + w - w ^ 2) +
      (w ^ 2 + w * y + 1) * ((1 - y) * (1 + w)) = 1 := by sorry
