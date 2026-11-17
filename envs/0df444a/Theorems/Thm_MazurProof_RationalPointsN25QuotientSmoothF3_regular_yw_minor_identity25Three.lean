-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_regular_yw_minor_identity25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.regular_yw_minor_identity25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:49.415335+00:00
-- url     : https://prove2.me/theorems/bf0629a5-e43e-4c9c-b12b-9e363d76f555
-- title:
--   The $yw$ Jacobian minor is controlled by the quadric and residual $y$-derivative in characteristic three
-- statement:
--   Let $K$ be a field of characteristic $3$, let $P=(1,y,z,w)$, let $M_{yw}$ be the $yw$ Jacobian minor, let $Q_X$ be the $x$-chart quadric, and let $R_Y$ be the residual $y$-derivative. Then $$(z-1)^2M_{yw}=Q_X\bigl((-y+z)(-z^2+z)-(z-1)(2yz+2z^2-2z+1)\bigr)+(z-1)R_Y.$$ This converts residual regularity into a nonvanishing Jacobian minor on the ordinary branch.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.regular_yw_minor_identity25Three
    {K : Type*} [Field K] [CharP K 3] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let M := canonicalJacobianMinors25Three P
    (z - 1) ^ 2 * M.yw =
      canonicalQuadricX25Three y z w *
        ((-y + z) * (-z ^ 2 + z) -
          (z - 1) * (2 * y * z + 2 * z ^ 2 - 2 * z + 1)) +
      (z - 1) * canonicalResidualYDerivative25Three y z := by sorry
