-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_hilbertBurch_exact
-- name    : MohP3.HilbertBurch.hilbertBurch_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:32.491911+00:00
-- url     : https://prove2.me/theorems/f9290158-946e-4fc2-8644-ee0f4c2eda53
-- title:
--   Hilbert Burch: hilbert Burch exact
-- statement:
--   **The exact complex** `0 → S^3 --Φ--> S^4 --(f_i)--> S --> S/J → 0`:
--   `Φ` is injective, exactness at `S^4`, exactness at `S`, and `S → S/J` is surjective.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L433-L443
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L433-L443

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

theorem MohP3.HilbertBurch.hilbertBurch_exact :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (Ideal.Quotient.mkₐ k (J k)) ∧
      Function.Surjective (Ideal.Quotient.mkₐ k (J k)) := by sorry
