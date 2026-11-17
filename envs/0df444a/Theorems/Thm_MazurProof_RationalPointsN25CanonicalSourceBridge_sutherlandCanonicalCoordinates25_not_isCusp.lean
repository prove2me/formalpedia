-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalCoordinates25_not_isCusp
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_not_isCusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:08.029753+00:00
-- url     : https://prove2.me/theorems/d15a7589-937f-49b8-b26d-3e739fbd38df
-- title:
--   A Sutherland source point with $y≠1$ maps to a noncuspidal canonical point
-- statement:
--   Let $x,y∈ℚ$ satisfy the Sutherland plane equation for $X_1(25)$, and assume $y≠1$. Then the associated canonical coordinate point is not a cusp: $$P_{Suth}(x,y)∉Cusp_{25}.$$ This transfers noncuspidality from the affine source model to the canonical model.
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

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_not_isCusp
    {x y : ℚ} (hsource : sutherlandX1Plane25 x y = 0) (hy1 : y ≠ 1) :
    ¬ IsCusp25 (sutherlandCanonicalCoordinates25 x y) := by sorry
