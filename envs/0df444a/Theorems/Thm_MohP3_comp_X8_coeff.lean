-- Prove2me | Theorems.Thm_MohP3_comp_X8_coeff
-- name    : MohP3.comp_X8_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:40.239298+00:00
-- url     : https://prove2.me/theorems/b17c042e-1592-4ffc-b684-32367e5bc083
-- title:
--   Moh P3: comp X8 coeff
-- statement:
--   The coefficients of `p.comp (X^8)` are supported on multiples of `8`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L32-L38
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L32-L38

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.comp_X8_coeff (p : ℚ[X]) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X^8)).coeff n = 0 := by sorry
