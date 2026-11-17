-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_nonzero
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_nonzero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:37.903103+00:00
-- url     : https://prove2.me/theorems/871a1b09-ef0c-438c-a791-5166f0940439
-- title:
--   Admissible order-$25$ Tate parameters give a nonzero canonical quadruple
-- statement:
--   Let $b,c∈ℚ$ satisfy $b≠0$, $F_5(b,c)≠0$, and $F_{25}(b,c)=0$. Let $(x,y,z,w)$ be the canonical coordinate quadruple constructed from $(b,c)$. Then $$\neg(x=0∧y=0∧z=0∧w=0).$$ This ensures that the constructed coordinates define a projective point rather than the zero vector.
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

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_nonzero
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    NonzeroQuadruple
      (tateCanonicalCoordinates25 b c).x
      (tateCanonicalCoordinates25 b c).y
      (tateCanonicalCoordinates25 b c).z
      (tateCanonicalCoordinates25 b c).w := by sorry
