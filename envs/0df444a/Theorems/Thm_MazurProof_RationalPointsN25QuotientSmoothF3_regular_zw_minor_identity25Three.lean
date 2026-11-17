-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_regular_zw_minor_identity25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.regular_zw_minor_identity25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:32.739196+00:00
-- url     : https://prove2.me/theorems/e5c38f0a-ef25-4840-a977-292ee8e70929
-- title:
--   The $zw$ Jacobian minor is controlled by the residual $z$-derivative in characteristic three
-- statement:
--   Let $K$ be a field of characteristic $3$, let $P=(1,y,z,w)$, let $M_{zw}$ be the $zw$ Jacobian minor, let $Q_X,C_X$ be the $x$-chart quadric and cubic, and let $R_Z$ be the residual $z$-derivative. Then $$(z-1)^2M_{zw}=Q_X\bigl((y+w-1)(-z^2+z)-(z-1)(y^2+yz+zw+y+w-1)\bigr)+(z-1)R_Z+2(z-1)^2C_X.$$ This supplies the second minor identity needed on the regular branch.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.regular_zw_minor_identity25Three
    {K : Type*} [Field K] [CharP K 3] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let M := canonicalJacobianMinors25Three P
    (z - 1) ^ 2 * M.zw =
      canonicalQuadricX25Three y z w *
        ((y + w - 1) * (-z ^ 2 + z) -
          (z - 1) * (y ^ 2 + y * z + z * w + y + w - 1)) +
      (z - 1) * canonicalResidualZDerivative25Three y z +
      2 * (z - 1) ^ 2 * canonicalCubicX25Three y z w := by sorry
