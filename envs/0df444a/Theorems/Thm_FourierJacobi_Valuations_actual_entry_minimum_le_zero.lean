-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_le_zero
-- name    : FourierJacobi.Valuations.actual_entry_minimum_le_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:14.043203+00:00
-- url     : https://prove2.me/theorems/e1981e69-eb37-51ae-adec-cd2d68a5f5ef
-- title:
--   Valuations: actual entry minimum le zero
-- statement:
--   The Valuations construction uses the actual entry minimum le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L102-L105
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L102-L105

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

theorem FourierJacobi.Valuations.actual_entry_minimum_le_zero (v : AddValuation K (WithTop ℤ))
    (a x y z : K) : matrixMinimum v (g a x y z) ≤ 0 := by sorry
