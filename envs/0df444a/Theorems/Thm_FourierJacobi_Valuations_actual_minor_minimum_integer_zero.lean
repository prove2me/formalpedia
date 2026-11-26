-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_integer_zero
-- name    : FourierJacobi.Valuations.actual_minor_minimum_integer_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:42.668829+00:00
-- url     : https://prove2.me/theorems/0cd5b91a-d8d8-47aa-a870-5c65e40b9d08
-- title:
--   Valuations: actual minor minimum integer zero
-- statement:
--   Specialization of the actual minor minimum when the central coordinate is zero.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L130-L136
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L130-L136

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

theorem FourierJacobi.Valuations.actual_minor_minimum_integer_zero (v : AddValuation K (WithTop ℤ))
    (a x y : K) (k j h c : ℤ) (hk : v a = k) (hj : v x = j) (hh : v y = h)
    (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y 0)) = (minorMinimum 0 k j h c : WithTop ℤ) := by sorry
