-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_phi_minors
-- name    : MohP3.HilbertBurch.phi_minors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:27.406806+00:00
-- url     : https://prove2.me/theorems/44524245-d5d5-494e-b904-48c802dc796b
-- title:
--   Hilbert Burch: phi minors
-- statement:
--   Direct expansion: `det Φ_{\hat i} = 6 (-1)^{i-1} f_i` (0-indexed here).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L49-L55
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L49-L55

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

theorem MohP3.HilbertBurch.phi_minors {A : Type*} [CommRing A] (x y z : A) :
    maximalMinor (phi x y z) =
      ![6*Gen.f1 x y z,-6*Gen.f2 x y z,6*Gen.f3 x y z,-6*Gen.f4 x y z] := by sorry
