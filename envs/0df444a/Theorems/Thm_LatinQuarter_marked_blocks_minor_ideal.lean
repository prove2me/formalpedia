-- Prove2me | Theorems.Thm_LatinQuarter_marked_blocks_minor_ideal
-- name    : LatinQuarter.marked_blocks_minor_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:16.932469+00:00
-- url     : https://prove2.me/theorems/5c10c2a1-5b7e-41fe-9fcb-2012d076f87c
-- title:
--   Latin Quarter: marked blocks minor ideal
-- statement:
--   One block elimination gives a common ideal for all the minors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L39-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L39-L72

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

theorem LatinQuarter.marked_blocks_minor_ideal {k h : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0) :
    ∃ z : Fin h × Fin h → R,
      (∀ j, z j * z j = 0) ∧
      ∀ t, AllMinorsIn (Matrix.fromBlocks A B C D) t
        (Ideal.span (Set.range z) ^ (t - k)) := by sorry
