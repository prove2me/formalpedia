-- Prove2me | Theorems.Thm_MohP3_dvd8_ntd
-- name    : MohP3.dvd8_ntd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:41.360088+00:00
-- url     : https://prove2.me/theorems/a2f36205-fb72-42ce-8002-9ab2ad2bc117
-- title:
--   Moh P3: dvd8 ntd
-- statement:
--   The Moh P3 construction uses the dvd8 ntd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L47-L50
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L47-L50

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.dvd8_ntd {p : ℚ[X]} (hp : p ≠ 0) : 8 ∣ (p.comp (X^8)).natTrailingDegree := by sorry
