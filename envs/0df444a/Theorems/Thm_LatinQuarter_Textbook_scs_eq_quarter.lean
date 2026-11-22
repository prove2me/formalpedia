-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_scs_eq_quarter
-- name    : LatinQuarter.Textbook.scs_eq_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:51.568889+00:00
-- url     : https://prove2.me/theorems/2057d959-750c-4233-bef1-346692967377
-- title:
--   Textbook: scs eq quarter
-- statement:
--   **Theorem B.** For every `n ≥ 1`, `scs(n) = scs(B_n) = ⌊n²/4⌋`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L245-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L245-L261

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_scs_eq_quarter

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.scs_eq_quarter (n : ℕ) (hn : 0 < n) :
    scs n = n * n / 4 ∧ scsOf (cyclicSquare n) = n * n / 4 := by sorry
