-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_integer_nonzero
-- name    : FourierJacobi.Valuations.actual_entry_minimum_integer_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:40.991795+00:00
-- url     : https://prove2.me/theorems/505c5bb7-563c-41db-849a-65bdf930c669
-- title:
--   Valuations: actual entry minimum integer nonzero
-- statement:
--   The Valuations construction uses the actual entry minimum integer nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L138-L143
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L138-L143

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

theorem FourierJacobi.Valuations.actual_entry_minimum_integer_nonzero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (r k j h : ℤ) (hr : r ≠ 0)
    (hk : v a = k) (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ)) :
    matrixMinimum v (g a x y z) = (entryMinimum r k j h : WithTop ℤ) := by sorry
