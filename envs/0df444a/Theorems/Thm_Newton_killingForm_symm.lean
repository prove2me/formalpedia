-- Prove2me | Theorems.Thm_Newton_killingForm_symm
-- name    : Newton.killingForm_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:47:41.026035+00:00
-- url     : https://prove2.me/theorems/92c79a7a-010b-5e7c-b9ea-a4bc5718f111
-- title:
--   Newton: killing Form symm
-- statement:
--   Killing form is symmetric
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L303-L306
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L303-L306

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

theorem Newton.killingForm_symm [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = killingForm B A := by sorry
