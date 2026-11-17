-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_residual_regular_bezout25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.residual_regular_bezout25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:30.136+00:00
-- url     : https://prove2.me/theorems/96044a0d-1c53-4a9b-b80b-968415833401
-- title:
--   A residual Bézout identity controls the characteristic-three singular locus away from $z=1$
-- statement:
--   Let $K$ be a field of characteristic $3$, and let $R_X(y,z)$ be the residual equation with partial derivatives $R_Y(y,z)$ and $R_Z(y,z)$. Define $$A=-y^2z^2-y^2z-y^2-yz^3+yz^2+y+z^4-z^3-z^2-1,$$ $$B=y^3z+y^3+y^2z^2+y^2z-yz^3+yz^2+yz-y+z^3-z^2-z-1,$$ and $$C=y^2z^3+yz^4+yz^3+yz^2+yz+y-z^5-z^4-z^3-z^2+z-1.$$ Then $$A R_X+B R_Y+C R_Z=z-1.$$ This forces a residual singular point into the exceptional branch $z=1$.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.residual_regular_bezout25Three
    {K : Type*} [Field K] [CharP K 3] (y z : K) :
    (-y ^ 2 * z ^ 2 - y ^ 2 * z - y ^ 2 - y * z ^ 3 + y * z ^ 2 +
        y + z ^ 4 - z ^ 3 - z ^ 2 - 1) *
        canonicalResidualX25Three y z +
      (y ^ 3 * z + y ^ 3 + y ^ 2 * z ^ 2 + y ^ 2 * z - y * z ^ 3 +
        y * z ^ 2 + y * z - y + z ^ 3 - z ^ 2 - z - 1) *
        canonicalResidualYDerivative25Three y z +
      (y ^ 2 * z ^ 3 + y * z ^ 4 + y * z ^ 3 + y * z ^ 2 + y * z + y -
        z ^ 5 - z ^ 4 - z ^ 3 - z ^ 2 + z - 1) *
        canonicalResidualZDerivative25Three y z = z - 1 := by sorry
