-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_phi_signedMinors
-- name    : MohP3.HilbertBurch.phi_signedMinors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:20.833653+00:00
-- url     : https://prove2.me/theorems/b0f2ef7d-2f8c-5a45-8112-a0a92e5e71e2
-- title:
--   Hilbert Burch: phi signed Minors
-- statement:
--   The Hilbert Burch construction uses the phi signed Minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L315-L319
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L315-L319

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
open MvPolynomial
variable {A : Type*} [CommRing A]

theorem MohP3.HilbertBurch.phi_signedMinors (x y z : A) (i : Fin 4) :
    (-1) ^ (i : ℕ) * maximalMinor (phi x y z) i = 6 * fvec x y z i := by sorry
