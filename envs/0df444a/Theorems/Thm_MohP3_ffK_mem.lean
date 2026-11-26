-- Prove2me | Theorems.Thm_MohP3_ffK_mem
-- name    : MohP3.ffK_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:03:05.021685+00:00
-- url     : https://prove2.me/theorems/94aa6f67-be12-400e-acdd-f0b0a91c7e9d
-- title:
--   Moh P3: ff K mem
-- statement:
--   The Moh P3 construction uses the ff K mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L87-L89
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L87-L89

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
omit [CharZero k]

theorem MohP3.ffK_mem (j : Fin 4) : ffK k j ∈ Ppoly k := by sorry
