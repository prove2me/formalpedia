-- Prove2me | Theorems.Thm_MohP3_ntd_X_pow_mul
-- name    : MohP3.ntd_X_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:39.632796+00:00
-- url     : https://prove2.me/theorems/48d223b2-fdaf-5de3-86fd-cec1f025df02
-- title:
--   Moh P3: ntd X pow mul
-- statement:
--   The Moh P3 construction uses the ntd X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L52-L56
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L52-L56

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.ntd_X_pow_mul (n : ℕ) (w : ℚ[X]) (hw : w.coeff 0 ≠ 0) :
    ((X:ℚ[X])^n * w).natTrailingDegree = n := by sorry
