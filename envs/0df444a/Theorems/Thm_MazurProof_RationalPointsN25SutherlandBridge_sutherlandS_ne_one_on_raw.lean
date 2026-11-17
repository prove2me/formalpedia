-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandS_ne_one_on_raw
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandS_ne_one_on_raw
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:10.611398+00:00
-- url     : https://prove2.me/theorems/3a70464b-45e3-4984-b8d1-6a6ef303b3fd
-- title:
--   A raw Sutherland point with $r≠1$ cannot have $s=1$
-- statement:
--   Let $r,s∈ℚ$ satisfy the raw Sutherland equation, and assume $r≠1$. Then $$s≠1.$$ This excludes a boundary value at which the optimized coordinate transformation degenerates.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandS_ne_one_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) : s ≠ 1 := by sorry
