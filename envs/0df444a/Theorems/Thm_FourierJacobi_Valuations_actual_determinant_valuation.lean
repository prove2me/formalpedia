-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_determinant_valuation
-- name    : FourierJacobi.Valuations.actual_determinant_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:18.090246+00:00
-- url     : https://prove2.me/theorems/869fde8b-4605-4eab-830d-c19b9e3490f3
-- title:
--   Valuations: actual determinant valuation
-- statement:
--   The collision determinant valuation is proved from the actual field ratio.
--   This is the algebraic part of `expanded:collision`, before its measure calculation.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L165-L186
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L165-L186

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

theorem FourierJacobi.Valuations.actual_determinant_valuation (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (hc : 2 * h = j - r → v (y ^ 2 / (x * z) - 1) = c) :
    v (y ^ 2 - x * z) = (determinantValuation r j h c : WithTop ℤ) := by sorry
