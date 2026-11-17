-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_not_isCusp
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_not_isCusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:52.93136+00:00
-- url     : https://prove2.me/theorems/2c38fd08-6c83-409b-8a29-1bd2d514dec8
-- title:
--   Admissible order-$25$ Tate parameters give a noncuspidal canonical point
-- statement:
--   Let $b,c∈ℚ$ satisfy $b≠0$, $F_5(b,c)≠0$, and $F_{25}(b,c)=0$. For the associated canonical point $P_{b,c}$, $$P_{b,c}\text{ is not a cusp}.$$ This distinguishes the point arising from a genuine elliptic curve with $25$-torsion from the cuspidal boundary.
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

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_not_isCusp
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    ¬ IsCusp25 (tateCanonicalCoordinates25 b c) := by sorry
