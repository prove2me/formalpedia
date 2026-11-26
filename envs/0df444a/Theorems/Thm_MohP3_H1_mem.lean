-- Prove2me | Theorems.Thm_MohP3_H1_mem
-- name    : MohP3.H1_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:05.788655+00:00
-- url     : https://prove2.me/theorems/07a77bd8-8854-541d-b8f4-de4f0cf587fb
-- title:
--   Moh P3: H1 mem
-- statement:
--   The Moh P3 construction uses the H1 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Defs.lean#L91-L91
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Defs.lean#L91-L91

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.H1_mem : H1 ∈ Q := by sorry
