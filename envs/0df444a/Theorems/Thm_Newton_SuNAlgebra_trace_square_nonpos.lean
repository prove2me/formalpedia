-- Prove2me | Theorems.Thm_Newton_SuNAlgebra_trace_square_nonpos
-- name    : Newton.SuNAlgebra.trace_square_nonpos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:47:28.66153+00:00
-- url     : https://prove2.me/theorems/b37b9eff-e0d1-42ae-a7c9-c3b88249bd74
-- title:
--   Su NAlgebra: trace square nonpos
-- statement:
--   Square of an su(N) element has non-positive trace (Tr(A²) ≤ 0)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L288-L296
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/LieAlgebra.lean#L288-L296

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

theorem Newton.SuNAlgebra.trace_square_nonpos (A : SuNAlgebra N) :
    (trace (A.matrix * A.matrix)).re ≤ 0 := by sorry
