-- Prove2me | Theorems.Thm_LatinQuarter_isUnit_det_of_square_map_eq_one
-- name    : LatinQuarter.isUnit_det_of_square_map_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:02.606621+00:00
-- url     : https://prove2.me/theorems/8dd4ebd5-fb68-490e-a4e1-b77aec3cba7f
-- title:
--   Latin Quarter: is Unit det of square map eq one
-- statement:
--   Marked top-left block entries square to the identity, so that block
--   is invertible even though the coefficient ring is not a field.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L29-L36
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Vanishing.lean#L29-L36

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

theorem LatinQuarter.isUnit_det_of_square_map_eq_one {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (hA : squareHom.mapMatrix A = 1) : IsUnit A.det := by sorry
