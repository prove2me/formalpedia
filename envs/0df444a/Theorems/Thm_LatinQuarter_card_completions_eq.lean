-- Prove2me | Theorems.Thm_LatinQuarter_card_completions_eq
-- name    : LatinQuarter.card_completions_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:18.960184+00:00
-- url     : https://prove2.me/theorems/697c62ab-0e50-4beb-b32c-8b427336b034
-- title:
--   Latin Quarter: card completions eq
-- statement:
--   The completions are in bijection with the Latin row choices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Parity.lean#L75-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Parity.lean#L75-L91

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
open Classical

theorem LatinQuarter.card_completions_eq {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (hL : IsLatin L) :
    (completions P L).card =
      (Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card := by sorry
