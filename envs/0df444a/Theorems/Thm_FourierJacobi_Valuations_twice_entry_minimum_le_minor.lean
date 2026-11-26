-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_twice_entry_minimum_le_minor
-- name    : FourierJacobi.Valuations.twice_entry_minimum_le_minor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:28.899293+00:00
-- url     : https://prove2.me/theorems/0f0f282c-1e40-4852-a4b8-d5736b975d24
-- title:
--   Valuations: twice entry minimum le minor
-- statement:
--   The ultrametric minor bound, for arbitrary actual matrices including zeros.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L91-L100
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L91-L100

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

theorem FourierJacobi.Valuations.twice_entry_minimum_le_minor (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin 4) (Fin 4) K) :
    matrixMinimum v A + matrixMinimum v A ≤ matrixMinimum v (secondCompound A) := by sorry
