-- Prove2me | Theorems.Thm_Newton_Complex_re_finset_sum
-- name    : Newton.Complex.re_finset_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:52:51.015799+00:00
-- url     : https://prove2.me/theorems/b5f34a42-026a-41e9-bb1a-a182231662b9
-- title:
--   Complex: re finset sum
-- statement:
--   Real part of a sum equals sum of real parts
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L230-L235
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L230-L235

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

theorem Newton.Complex.re_finset_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by sorry
