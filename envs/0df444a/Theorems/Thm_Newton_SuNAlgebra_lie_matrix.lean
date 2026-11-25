-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_lie_matrix
-- name    : Newton.SuNAlgebra.lie_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:41.375769+00:00
-- url     : https://prove2.me/theorems/5df12c27-1a1f-42b6-817c-88fc72b210c5
-- title:
--   Su NAlgebra: lie matrix
-- statement:
--   Matrix representation of Lie bracket
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L203-L204
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L203-L204

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

theorem Newton.SuNAlgebra.lie_matrix (A B : SuNAlgebra N) :
    (⁅A, B⁆ : SuNAlgebra N).matrix = ⁅A.matrix, B.matrix⁆ := by sorry

attribute [defeq] Newton.SuNAlgebra.lie_matrix
