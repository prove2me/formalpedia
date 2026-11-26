-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_le_matrixMinimum_iff
-- name    : FourierJacobi.Valuations.le_matrixMinimum_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:07.857859+00:00
-- url     : https://prove2.me/theorems/79342e46-6b31-4237-afd1-7a3d8cd19983
-- title:
--   Valuations: le matrix Minimum iff
-- statement:
--   The Valuations construction uses the le matrix Minimum iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L29-L32
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L29-L32

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

theorem FourierJacobi.Valuations.le_matrixMinimum_iff {n m : ℕ} (v : AddValuation K (WithTop ℤ))
    (A : Matrix (Fin n) (Fin m) K) (b : WithTop ℤ) :
    b ≤ matrixMinimum v A ↔ ∀ i j, b ≤ v (A i j) := by sorry
