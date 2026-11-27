-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_det_augment
-- name    : MohP3.HilbertBurch.det_augment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:34.54796+00:00
-- url     : https://prove2.me/theorems/7647262b-465e-42b9-b7a6-022d99026bea
-- title:
--   Hilbert Burch: det augment
-- statement:
--   Laplace expansion of `det [a | Φ]` along its first column.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L89-L94
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L89-L94

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

theorem MohP3.HilbertBurch.det_augment (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) :
    (augment a Φ).det = ∑ i : Fin 4, (-1) ^ (i : ℕ) * a i * maximalMinor Φ i := by sorry
