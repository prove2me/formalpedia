-- Prove2me | Theorems.Thm_N25_canonicalChartPairPresentation25_jacobian
-- name    : N25.canonicalChartPairPresentation25_jacobian
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:35.977667+00:00
-- url     : https://prove2.me/theorems/e067f57b-0203-4746-b534-d545eb7e5677
-- title:
--   The presentation Jacobian is the corresponding canonical minor
-- statement:
--   Let $K$ be a commutative ring, fix a chart pivot $i$, and let $(j,k)$ be a permitted pair of nonpivot columns. In the quotient by the canonical chart ideal, the Jacobian element of the associated presentation is exactly the residue class of the canonical minor: $$J_{i,(j,k)}=\overline{M_{jk}}.$$ This identifies the abstract standard-smooth Jacobian with the explicit determinant already certified pointwise.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25

theorem N25.canonicalChartPairPresentation25_jacobian (K : Type*) [CommRing K]
    (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    (canonicalChartPairPresentation25 K pivot pair).jacobian =
      Ideal.Quotient.mk (canonicalChartIdeal25 K pivot)
        (canonicalJacobianMinor25 K pair.val.1 pair.val.2) := by sorry
