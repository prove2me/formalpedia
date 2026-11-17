-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateR_ne_one
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateR_ne_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:40.545945+00:00
-- url     : https://prove2.me/theorems/d29ce024-76d5-4e5c-9567-604a19ae9ade
-- title:
--   The Tate-to-Sutherland coordinate $b/c$ is not equal to one
-- statement:
--   Let $b,c∈ℚ$ with $c≠0$ and $b-c≠0$. Then $$b/c≠1.$$ This verifies the nondegeneracy condition required by the raw Sutherland analysis.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateR_ne_one {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0) : b / c ≠ 1 := by sorry
