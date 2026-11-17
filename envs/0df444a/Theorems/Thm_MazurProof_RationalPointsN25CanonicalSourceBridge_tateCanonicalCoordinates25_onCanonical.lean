-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_onCanonical
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_onCanonical
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:12.392533+00:00
-- url     : https://prove2.me/theorems/8993579f-1a75-4f9d-8171-be2f8c1257cd
-- title:
--   Admissible order-$25$ Tate parameters lie on the canonical curve
-- statement:
--   Let $b,c∈ℚ$ satisfy $b≠0$, $F_5(b,c)≠0$, and $F_{25}(b,c)=0$. If $P_{b,c}$ denotes the associated canonical coordinate quadruple, then $$P_{b,c}\text{ lies on the canonical level-$25$ curve}.$$ Equivalently, its canonical quadric and cubic equations both vanish; this places the Tate source point on the genus-$4$ canonical model used before quotienting.
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
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25CanonicalSourceBridge
open RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_onCanonical
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    OnCanonical25 (tateCanonicalCoordinates25 b c) := by sorry
