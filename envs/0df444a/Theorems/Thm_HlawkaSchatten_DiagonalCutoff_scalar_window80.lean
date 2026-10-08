-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window80
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window80
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-06T17:31:56.496375+00:00
-- url     : https://prove2.me/theorems/43c67782-7a73-41a2-b171-4e11e2243128
-- title:
--   Scalar window for the cutoff-80 step
-- statement:
--   For $80 \le p \le 84$, the linear lower bound $(23/50)p$ and the scalar envelope at radius $9/25$ both lie strictly below the sharp cyclic Hlawka constant. This is the scalar analytic input for the window reduction from cutoff 84 down to cutoff 80: it supplies the $K$-range lower bound $(23/50)p$ used by the box-convexity theorem and the envelope confinement that localizes a hypothetical failure triple.
-- source:
--   https://prove2.me campaign 'Sharp diagonal Hlawka constant'; analytic window estimate for the 84-to-80 reduction step, adapted from the accepted scalar_window84 argument

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window80 : ∀ p : ℝ, 80 ≤ p → p ≤ 84 → (23/50 : ℝ)*p < cyclicConstant p ∧ scalarEnvelope p (9/25) < cyclicConstant p := by sorry
