-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalXW_not_both_zero
-- name    : MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalXW_not_both_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:34.445146+00:00
-- url     : https://prove2.me/theorems/f87dac4b-3962-4b9a-92a9-3bb332ee7570
-- title:
--   Away from $y=1$, the Sutherland canonical $X$ and $W$ coordinates are not both zero
-- statement:
--   Let $x,y∈ℚ$ and assume $y≠1$. For the canonical coordinates obtained from the Sutherland model, $$X_{25}(x,y)≠0\quad\text{or}\quad W_{25}(x,y)≠0.$$ This prevents the constructed projective quadruple from collapsing on the relevant source open.
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

theorem MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalXW_not_both_zero
    {x y : ℚ} (hy1 : y ≠ 1) :
    sutherlandCanonicalX25 x y ≠ 0 ∨ sutherlandCanonicalW25 x y ≠ 0 := by sorry
