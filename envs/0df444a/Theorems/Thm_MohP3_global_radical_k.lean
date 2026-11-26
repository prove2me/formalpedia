-- Prove2me | Theorems.Thm_MohP3_global_radical_k
-- name    : MohP3.global_radical_k
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:05:17.745985+00:00
-- url     : https://prove2.me/theorems/a6524d4c-df8c-425f-a655-13d300a44414
-- title:
--   Moh P3: global radical k
-- statement:
--   **The set-theoretic complete intersection statement over an arbitrary
--   characteristic-zero field.**
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L286-L292
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L286-L292

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.global_radical_k : Ideal.radical (Qpoly k) = Ppoly k := by sorry
