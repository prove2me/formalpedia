-- Prove2me | Theorems.Thm_LatinQuarter_small_clue_coefficient_zero
-- name    : LatinQuarter.small_clue_coefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:45.890029+00:00
-- url     : https://prove2.me/theorems/b4d20b88-08f7-44c6-ad8d-cfb63c90ed7e
-- title:
--   Latin Quarter: small clue coefficient zero
-- statement:
--   Below the quarter bound, any balanced choice of marked positions makes the
--   completion polynomial's highest square-free coefficient vanish. No Latin condition
--   on the reference square is required.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/LowerBound.lean#L25-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/LowerBound.lean#L25-L46

module
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial

theorem LatinQuarter.small_clue_coefficient_zero {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n) (hP : P.card < n * n / 4) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s)) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s))).coeff
      (allTagsExponent (Cell n)) = 0 := by sorry
