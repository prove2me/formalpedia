-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_minima_finite
-- name    : FourierJacobi.Valuations.actual_minima_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:09.317373+00:00
-- url     : https://prove2.me/theorems/e32a40ae-5246-490b-b2c9-beadeebedd71
-- title:
--   Valuations: actual minima finite
-- statement:
--   The extrema are finite even when some coordinates or the determinant vanish.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L114-L120
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L114-L120

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]

theorem FourierJacobi.Valuations.actual_minima_finite (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (g a x y z) ≠ ⊤ ∧
      matrixMinimum v (secondCompound (g a x y z)) ≠ ⊤ := by sorry
