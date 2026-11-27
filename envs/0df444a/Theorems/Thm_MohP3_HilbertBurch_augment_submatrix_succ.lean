-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_augment_submatrix_succ
-- name    : MohP3.HilbertBurch.augment_submatrix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:45.122596+00:00
-- url     : https://prove2.me/theorems/ae6c63b8-a696-422e-bc91-5a927719f659
-- title:
--   Hilbert Burch: augment submatrix succ
-- statement:
--   The Hilbert Burch construction uses the augment submatrix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L83-L86
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L83-L86

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S]
omit [CommRing S]

theorem MohP3.HilbertBurch.augment_submatrix_succ (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4) :
    (augment a Φ).submatrix i.succAbove Fin.succ = Φ.submatrix i.succAbove id := by sorry
