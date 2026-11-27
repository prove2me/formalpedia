-- Prove2me | Theorems.Thm_MohP3_good_mul_z
-- name    : MohP3.good_mul_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:17.834634+00:00
-- url     : https://prove2.me/theorems/559cb444-4dea-5c36-94ff-a050a91ce479
-- title:
--   Moh P3: good mul z
-- statement:
--   The Moh P3 construction uses the good mul z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Kernel.lean#L96-L107
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Kernel.lean#L96-L107

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.good_mul_z {g : R} (h : Good g) : Good (z * g) := by sorry
