-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum
-- name    : FourierJacobi.Valuations.actual_entry_minimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:49.839785+00:00
-- url     : https://prove2.me/theorems/b1285219-7168-4e41-b38a-f65c285b0708
-- title:
--   Valuations: actual entry minimum
-- statement:
--   The Valuations construction uses the actual entry minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L49-L65
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L49-L65

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

theorem FourierJacobi.Valuations.actual_entry_minimum (v : AddValuation K (WithTop ℤ)) (a x y z : K) :
    matrixMinimum v (g a x y z) = entryListMinimum v a x y z := by sorry
