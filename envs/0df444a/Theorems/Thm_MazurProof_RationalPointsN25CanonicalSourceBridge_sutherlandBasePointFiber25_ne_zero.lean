-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandBasePointFiber25_ne_zero
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandBasePointFiber25_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:54.539919+00:00
-- url     : https://prove2.me/theorems/99cca407-e18e-469e-bacb-ed5cbd4626ff
-- title:
--   The Sutherland base-point fibre polynomial never vanishes over $ℚ$
-- statement:
--   For every rational number $y$, the explicit base-point fibre expression satisfies $$B_{25}(y)≠0.$$ This excludes the remaining degenerate source fibre in the canonical-coordinate construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25CanonicalSourceBridge
open RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandBasePointFiber25_ne_zero (y : ℚ) :
    sutherlandBasePointFiber25 y ≠ 0 := by sorry
