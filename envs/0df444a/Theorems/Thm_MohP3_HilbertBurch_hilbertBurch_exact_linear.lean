-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_hilbertBurch_exact_linear
-- name    : MohP3.HilbertBurch.hilbertBurch_exact_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:41:41.844388+00:00
-- url     : https://prove2.me/theorems/06ee0ea2-2058-480a-ae7c-c755b387f36f
-- title:
--   Hilbert Burch: hilbert Burch exact linear
-- statement:
--   The same complex, stated with `S`-linear maps: `Ideal.Quotient.mkₐ` viewed as the
--   `S`-linear quotient map `S → S ⧸ J` (`Submodule.mkQ`).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L447-L455
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L447-L455

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
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.HilbertBurch.hilbertBurch_exact_linear :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (J k).mkQ ∧
      Function.Surjective (J k).mkQ := by sorry
