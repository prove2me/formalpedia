-- Prove2me | Theorems.Thm_MohP3_K_comp_X8_coeff
-- name    : MohP3.K.comp_X8_coeff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:01:20.220324+00:00
-- url     : https://prove2.me/theorems/572eb6f1-b590-5d4c-96e5-b26c4cc88767
-- title:
--   K: comp X8 coeff
-- statement:
--   The coefficients of `p.comp (X^8)` are supported on multiples of `8`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L37-L43
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L37-L43

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}

theorem MohP3.K.comp_X8_coeff (p : Polynomial k) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X ^ 8)).coeff n = 0 := by sorry
