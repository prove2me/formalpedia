-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_ext_matrix
-- name    : Newton.SuNAlgebra.ext_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:45:10.813885+00:00
-- url     : https://prove2.me/theorems/15ae8d3c-7df0-4046-9b61-a2697183debd
-- title:
--   Su NAlgebra: ext matrix
-- statement:
--   If matrix is zero, then the element is zero
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L82-L83
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L82-L83

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
open Newton.SuNAlgebra

theorem Newton.SuNAlgebra.ext_matrix {A : SuNAlgebra N} (h : A.matrix = 0) : A = 0 := by sorry
