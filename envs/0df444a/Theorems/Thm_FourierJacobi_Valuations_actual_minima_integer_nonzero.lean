-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_minima_integer_nonzero
-- name    : FourierJacobi.Valuations.actual_minima_integer_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:24.647427+00:00
-- url     : https://prove2.me/theorems/9af78afe-6ca5-489d-8e42-a2fcb9fbc748
-- title:
--   Valuations: actual minima integer nonzero
-- statement:
--   Both intrinsic actual-matrix minima equal the integer-table inputs once
--   all relevant valuations are finite. The determinant valuation is derived,
--   not supplied as a hypothesis.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L205-L215
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L205-L215

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

theorem FourierJacobi.Valuations.actual_minima_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) ∧
      matrixMinimum v (secondCompound (g a x y z)) =
        (minorMinimum r k j h c : WithTop ℤ) := by sorry
