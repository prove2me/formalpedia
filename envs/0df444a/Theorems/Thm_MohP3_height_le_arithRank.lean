-- Prove2me | Theorems.Thm_MohP3_height_le_arithRank
-- name    : MohP3.height_le_arithRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:22.040261+00:00
-- url     : https://prove2.me/theorems/21b7e3d8-9ec9-44c2-8a29-55a833ac2a75
-- title:
--   Moh P3: height le arith Rank
-- statement:
--   **Krull's height theorem** gives the standard lower bound for the arithmetic
--   rank of a prime ideal of a Noetherian ring.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L54-L59
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L54-L59

module
public import Mathlib
public import Definitions.Def_MohP3_Ara
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3
variable {A : Type*} [CommRing A]

theorem MohP3.height_le_arithRank [IsNoetherianRing A] (p : Ideal A) (hp : p.IsPrime) :
    p.height ≤ arithRank p := by sorry
