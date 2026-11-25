-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_jacobi_identity_alt
-- name    : Newton.SuNAlgebra.jacobi_identity_alt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:08.7178+00:00
-- url     : https://prove2.me/theorems/df45c523-aeb2-449e-98df-4be056e22fa2
-- title:
--   Su NAlgebra: jacobi identity alt
-- statement:
--   Alternative form of Jacobi identity
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L217-L219
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L217-L219

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

theorem Newton.SuNAlgebra.jacobi_identity_alt (A B C : SuNAlgebra N) :
    ⁅A, ⁅B, C⁆⁆ = ⁅⁅A, B⁆, C⁆ + ⁅B, ⁅A, C⁆⁆ := by sorry
