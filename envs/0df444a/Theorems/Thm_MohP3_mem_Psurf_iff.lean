-- Prove2me | Theorems.Thm_MohP3_mem_Psurf_iff
-- name    : MohP3.mem_Psurf_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:28.370107+00:00
-- url     : https://prove2.me/theorems/fb958e57-1a6e-52bb-a000-c59295271541
-- title:
--   Moh P3: mem Psurf iff
-- statement:
--   The Moh P3 construction uses the mem Psurf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L88-L88
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L88-L88

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.mem_Psurf_iff {g : R} : g ∈ Psurf ↔ sigma g = 0 := by sorry
