-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_cofactor_column
-- name    : MohP3.HilbertBurch.cofactor_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:32.964938+00:00
-- url     : https://prove2.me/theorems/3a9effde-08d8-42fb-b87a-9a5f8e6c2d38
-- title:
--   Hilbert Burch: cofactor column
-- statement:
--   The cofactor identity `[a | Φ] · adj [a | Φ] = det • 1`, read in the `j`-th
--   column: `((-1)^j m_j) • a + Φ w = det • e_j` for an explicit `w`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L98-L114
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L98-L114

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

theorem MohP3.HilbertBurch.cofactor_column (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (j : Fin 4) :
    ∃ w : Fin 3 → S, ∀ r : Fin 4,
      a r * ((-1) ^ (j : ℕ) * maximalMinor Φ j) + (Φ *ᵥ w) r =
        if r = j then (augment a Φ).det else 0 := by sorry
