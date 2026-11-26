-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_heisenberg_rearrange
-- name    : FourierJacobi.LocalMatrix.heisenberg_rearrange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:18.230148+00:00
-- url     : https://prove2.me/theorems/1285cc50-7138-46a9-a80c-a767573f5c87
-- title:
--   Local Matrix: heisenberg rearrange
-- statement:
--   The Local Matrix construction uses the heisenberg rearrange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L61-L64
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L61-L64

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_Matrices
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.LocalMatrix
open Matrix
variable {K : Type*} [Field K]

theorem FourierJacobi.LocalMatrix.heisenberg_rearrange (y z u t : K) :
    YZ y z * X u * N (-t) 0 0 =
      N (-t) 0 0 * YZ (y - t * u) (z - t * u ^ 2) * X u := by sorry
