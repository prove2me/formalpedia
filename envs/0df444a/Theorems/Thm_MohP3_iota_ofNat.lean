-- Prove2me | Theorems.Thm_MohP3_iota_ofNat
-- name    : MohP3.iota_ofNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:20.59071+00:00
-- url     : https://prove2.me/theorems/53c04e4e-d5e6-5dc0-81cf-c75270b0b015
-- title:
--   Moh P3: iota of Nat
-- statement:
--   The Moh P3 construction uses the iota of Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L40-L41
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L40-L41

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.iota_ofNat (n : ℕ) [n.AtLeastTwo] :
    iota (no_index (OfNat.ofNat n)) = OfNat.ofNat n := by sorry
