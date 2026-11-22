-- Prove2me | Theorems.Thm_LatinQuarter_shifted_tags_product_vanishes
-- name    : LatinQuarter.shifted_tags_product_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:18.608002+00:00
-- url     : https://prove2.me/theorems/0c7185c2-6269-4b15-bede-468e71f0aca3
-- title:
--   Latin Quarter: shifted tags product vanishes
-- statement:
--   A version of the vanishing lemma allowing arbitrary finite sets of
--   selected rows and columns in each minor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Shifted.lean#L43-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Shifted.lean#L43-L90

module
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix

theorem LatinQuarter.shifted_tags_product_vanishes {N ι : Type*} [Fintype ι]
    {k h : ℕ} (e : Fin k ⊕ Fin h ≃ N)
    (α : ι → Type*) [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (r c : (i : ι) → α i → N)
    (hbudget : h * h < ∑ i, (Fintype.card (α i) - k)) :
    (∏ i, ((shiftedTags e).submatrix (r i) (c i)).det) = 0 := by sorry
