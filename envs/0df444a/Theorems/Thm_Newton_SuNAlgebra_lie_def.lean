-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_lie_def
-- name    : Newton.SuNAlgebra.lie_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:37.702238+00:00
-- url     : https://prove2.me/theorems/204eb02b-f59a-48ec-bd3d-e412a80493d8
-- title:
--   Su NAlgebra: lie def
-- statement:
--   Lie bracket expanded as commutator
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L207-L209
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L207-L209

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

theorem Newton.SuNAlgebra.lie_def (A B : SuNAlgebra N) :
    (⁅A, B⁆ : SuNAlgebra N).matrix = A.matrix * B.matrix - B.matrix * A.matrix := by sorry
