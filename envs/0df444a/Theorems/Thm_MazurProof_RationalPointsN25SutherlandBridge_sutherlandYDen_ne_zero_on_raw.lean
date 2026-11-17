-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandYDen_ne_zero_on_raw
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandYDen_ne_zero_on_raw
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:41.26014+00:00
-- url     : https://prove2.me/theorems/be368eef-c951-43cd-b2e3-c34da8c9a4ef
-- title:
--   The optimized $Y$-denominator is nonzero on the nondegenerate raw Sutherland locus
-- statement:
--   Let $r,s∈ℚ$ satisfy the raw Sutherland equation, with $s≠0$ and $s≠1$. Then $$s^2-s-r+1≠0.$$ This ensures that the raw-to-optimized $Y$-coordinate is defined.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor
set_option linter.style.longLine false

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandYDen_ne_zero_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : s ^ 2 - s - r + 1 ≠ 0 := by sorry
