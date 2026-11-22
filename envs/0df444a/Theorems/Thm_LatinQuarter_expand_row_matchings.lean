-- Prove2me | Theorems.Thm_LatinQuarter_expand_row_matchings
-- name    : LatinQuarter.expand_row_matchings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:05.700922+00:00
-- url     : https://prove2.me/theorems/0049b370-25a6-4da0-8314-942d964199f5
-- title:
--   Latin Quarter: expand row matchings
-- statement:
--   Expanding the row matching sums enumerates all independent ways to
--   finish the rows. The clue factors restore the full set of cells.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L37-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Counting.lean#L37-L61

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial

theorem LatinQuarter.expand_row_matchings {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) :
    clueProduct P L Y * rowMinorProduct P L Y =
      ∑ σ : RowChoices P, ∏ p : Cell n, Y p.2 (chosenSquare P L σ p.1 p.2) := by sorry
