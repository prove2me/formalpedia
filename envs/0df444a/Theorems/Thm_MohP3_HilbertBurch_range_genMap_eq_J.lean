-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_range_genMap_eq_J
-- name    : MohP3.HilbertBurch.range_genMap_eq_J
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:26.495515+00:00
-- url     : https://prove2.me/theorems/d5f63e0a-a3b3-4fa1-afbe-514e0425d2e7
-- title:
--   Hilbert Burch: range gen Map eq J
-- statement:
--   **3.** The image of the generator map is `J`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L427-L429
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L427-L429

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
omit [CharZero k]

theorem MohP3.HilbertBurch.range_genMap_eq_J : LinearMap.range (genMap k) = J k := by sorry
