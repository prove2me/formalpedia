-- Prove2me | Theorems.Thm_Newton_killingForm_add_left
-- name    : Newton.killingForm_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:50:02.835132+00:00
-- url     : https://prove2.me/theorems/b7b7a285-3a77-598e-a5c0-1d232b9583d1
-- title:
--   Newton: killing Form add left
-- statement:
--   Bilinearity of Killing form (left)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L309-L312
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L309-L312

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

theorem Newton.killingForm_add_left [DecidableEq (Fin N)] (A B C : SuNAlgebra N) :
    killingForm (A + B) C = killingForm A C + killingForm B C := by sorry
