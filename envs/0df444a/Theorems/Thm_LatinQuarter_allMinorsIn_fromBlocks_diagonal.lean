-- Prove2me | Theorems.Thm_LatinQuarter_allMinorsIn_fromBlocks_diagonal
-- name    : LatinQuarter.allMinorsIn_fromBlocks_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:34.393557+00:00
-- url     : https://prove2.me/theorems/6c91d4fd-ee98-472f-bca5-9f4eaf07f4eb
-- title:
--   Latin Quarter: all Minors In from Blocks diagonal
-- statement:
--   The lower block rows supply enough factors from the residual ideal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L77-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Minors.lean#L77-L114

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

theorem LatinQuarter.allMinorsIn_fromBlocks_diagonal {k h t : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (Z : Matrix (Fin h) (Fin h) R)
    (J : Ideal R) (hZ : ∀ i j, Z i j ∈ J) :
    AllMinorsIn (Matrix.fromBlocks A 0 0 Z) t (J ^ (t - k)) := by sorry
