-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_jacobi_identity
-- name    : Newton.SuNAlgebra.jacobi_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:45:36.286343+00:00
-- url     : https://prove2.me/theorems/934e5dfe-7629-58ee-bc0c-9b87dcdd57e4
-- title:
--   Su NAlgebra: jacobi identity
-- statement:
--   Jacobi identity follows from Mathlib's lie_jacobi
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L212-L214
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L212-L214

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

theorem Newton.SuNAlgebra.jacobi_identity (A B C : SuNAlgebra N) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = (0 : SuNAlgebra N) := by sorry
