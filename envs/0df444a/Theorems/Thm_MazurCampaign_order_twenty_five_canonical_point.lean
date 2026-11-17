-- Prove2me | Theorems.Thm_MazurCampaign_order_twenty_five_canonical_point
-- name    : MazurCampaign.order_twenty_five_canonical_point
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:12.738864+00:00
-- url     : https://prove2.me/theorems/49262016-e520-4f14-8c95-874b8a621ab0
-- title:
--   A rational point of order $25$ produces a noncuspidal rational point on the canonical model
-- statement:
--   Let $E/ℚ$ be an elliptic curve and let $x∈E(ℚ)_{tors}$ have additive order $25$. Then there exist $b,c∈ℚ$ such that the canonical coordinate quadruple $P_{b,c}$ is nonzero, lies on the canonical level-$25$ curve, and is not a cusp: $$∃b,c∈ℚ,\quad P_{b,c}≠0,\quad P_{b,c}∈C_{25},\quad P_{b,c}\notin Cusp_{25}.$$ This is the source-to-modular-curve bridge for the final contradiction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_TorsionDefs
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor

open MazurCampaign
open MazurProof
open MazurProof.RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction
open MazurProof.RationalPointsN25CanonicalSourceBridge

theorem MazurCampaign.order_twenty_five_canonical_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : RationalTorsion E) (hx : addOrderOf x = 25) :
    ∃ b c : ℚ,
      NonzeroQuadruple (tateCanonicalCoordinates25 b c).x
        (tateCanonicalCoordinates25 b c).y (tateCanonicalCoordinates25 b c).z
        (tateCanonicalCoordinates25 b c).w ∧
      OnCanonical25 (tateCanonicalCoordinates25 b c) ∧
      ¬ IsCusp25 (tateCanonicalCoordinates25 b c) := by sorry
