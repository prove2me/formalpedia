-- Prove2me | Theorems.Thm_LatinQuarter_det_mem_pow_of_rows
-- name    : LatinQuarter.det_mem_pow_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:33.335865+00:00
-- url     : https://prove2.me/theorems/6badf1b1-7ab9-4925-aa66-a08a0555f85c
-- title:
--   Latin Quarter: det mem pow of rows
-- statement:
--   A determinant with `s.card` rows in an ideal lies in that ideal power.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L61-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L61-L74

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]

theorem LatinQuarter.det_mem_pow_of_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (J : Ideal R) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j, M i j ∈ J) : M.det ∈ J ^ s.card := by sorry
