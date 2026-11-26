-- Prove2me | Theorems.Thm_MohP3_comp_X8_ne_zero
-- name    : MohP3.comp_X8_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:32.685698+00:00
-- url     : https://prove2.me/theorems/7aa71b5d-2f0f-505b-959b-8474c38ff7b8
-- title:
--   Moh P3: comp X8 ne zero
-- statement:
--   The Moh P3 construction uses the comp X8 ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L40-L45
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L40-L45

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.comp_X8_ne_zero {p : ℚ[X]} (hp : p ≠ 0) : p.comp (X^8) ≠ 0 := by sorry
