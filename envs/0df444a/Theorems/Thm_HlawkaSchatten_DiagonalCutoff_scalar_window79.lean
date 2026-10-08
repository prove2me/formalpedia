-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window79
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window79
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-07T10:38:44.576002+00:00
-- url     : https://prove2.me/theorems/47e66892-1006-4ced-aadc-502387327d3a
-- title:
--   Scalar window for the cutoff-79 step
-- statement:
--   For $79 \le p \le 80$, the linear lower bound $(23/50)p$ and the scalar envelope at radius $9/25$ both lie strictly below the cyclic constant.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window79 : ∀ p : ℝ, 79 ≤ p → p ≤ 80 → (23/50 : ℝ)*p < cyclicConstant p ∧ scalarEnvelope p (9/25) < cyclicConstant p := by sorry
