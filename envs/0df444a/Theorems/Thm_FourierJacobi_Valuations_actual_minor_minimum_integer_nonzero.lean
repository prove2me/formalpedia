-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_integer_nonzero
-- name    : FourierJacobi.Valuations.actual_minor_minimum_integer_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:48.684227+00:00
-- url     : https://prove2.me/theorems/97580bed-ff21-5406-8f5a-add6d2f0cb66
-- title:
--   Valuations: actual minor minimum integer nonzero
-- statement:
--   The only additional input needed for the integer minor table is the valuation
--   of the actual determinant polynomial; it is not a Cartan or period hypothesis.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L147-L156
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L147-L156

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

theorem FourierJacobi.Valuations.actual_minor_minimum_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h c : ℤ) (hr : r ≠ 0) (ha : a ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hd : v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ)) :
    matrixMinimum v (secondCompound (g a x y z)) = (minorMinimum r k j h c : WithTop ℤ) := by sorry
