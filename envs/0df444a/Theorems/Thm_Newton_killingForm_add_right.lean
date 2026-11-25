-- Prove2me | Theorems.Thm_Newton_killingForm_add_right
-- name    : Newton.killingForm_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:50:39.055719+00:00
-- url     : https://prove2.me/theorems/c2e8b52e-6900-46a1-a7cc-9ab4c8be0203
-- title:
--   Newton: killing Form add right
-- statement:
--   Bilinearity of Killing form (right)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L315-L318
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L315-L318

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_Newton_Gauge_LieAlgebra
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.killingForm_add_right [DecidableEq (Fin N)] (A B C : SuNAlgebra N) :
    killingForm A (B + C) = killingForm A B + killingForm A C := by sorry
