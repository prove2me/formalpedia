-- Prove2me | Theorems.Thm_LatinQuarter_marked_blocks_product_vanishes
-- name    : LatinQuarter.marked_blocks_product_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:17.346472+00:00
-- url     : https://prove2.me/theorems/bd737bb1-d8e5-48bf-9219-91fea7d2d971
-- title:
--   Latin Quarter: marked blocks product vanishes
-- statement:
--   The abstract vanishing lemma: more residual factors than residual
--   positions force a repeated square-zero entry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L76-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L76-L96

module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R] [CharP R 2]

theorem LatinQuarter.marked_blocks_product_vanishes {k h : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0)
    (t : ι → ℕ)
    (r c : (i : ι) → Fin (t i) → Fin k ⊕ Fin h)
    (hbudget : h * h < ∑ i, (t i - k)) :
    (∏ i, ((Matrix.fromBlocks A B C D).submatrix (r i) (c i)).det) = 0 := by sorry
