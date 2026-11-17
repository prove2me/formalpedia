-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalCoordinates25_quadric
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_quadric
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:41.20732+00:00
-- url     : https://prove2.me/theorems/12139e52-df9d-4a7e-a768-6c50b11dfc0b
-- title:
--   The canonical quadric pulls back to the Sutherland equation times an explicit cofactor
-- statement:
--   Let $x,y∈ℚ$, and let $P_{Suth}(x,y)$ be the associated canonical coordinate quadruple. Then $$Q_{25}(P_{Suth}(x,y))=C_Q(x,y)F_{Suth}(x,y),$$ where $C_Q$ is the explicit Sutherland-to-canonical quadric cofactor. This proves that every Sutherland source point satisfies the canonical quadric.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25CanonicalSourceBridge
open RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_quadric (x y : ℚ) :
    canonicalQuadric25
        (sutherlandCanonicalCoordinates25 x y).x
        (sutherlandCanonicalCoordinates25 x y).y
        (sutherlandCanonicalCoordinates25 x y).z
        (sutherlandCanonicalCoordinates25 x y).w =
      sutherlandCanonicalQuadricCofactor25 x y *
        sutherlandX1Plane25 x y := by sorry
