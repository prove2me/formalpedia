-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_range_phiMap_eq_ker_genMap
-- name    : MohP3.HilbertBurch.range_phiMap_eq_ker_genMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:12.717135+00:00
-- url     : https://prove2.me/theorems/fe78827b-2e9f-52d6-b65f-ec5cfb394963
-- title:
--   Hilbert Burch: range phi Map eq ker gen Map
-- statement:
--   **2.** The image of `Φ` is exactly the module of relations among `f1,…,f4`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L422-L423
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L422-L423

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

theorem MohP3.HilbertBurch.range_phiMap_eq_ker_genMap : LinearMap.range (phiMap k) = LinearMap.ker (genMap k) := by sorry
