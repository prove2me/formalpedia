-- Prove2me | Theorems.Thm_MohP3_indep
-- name    : MohP3.indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:45.385375+00:00
-- url     : https://prove2.me/theorems/9097c6ab-d93b-4cf0-bdcb-da12ea1c1537
-- title:
--   Moh P3: indep
-- statement:
--   The eight polynomials `vv i` are linearly independent over `ℚ[t^8]`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L78-L115
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L78-L115

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.indep (p : Fin 8 → ℚ[X]) (hs : ∑ i, (p i).comp (X^8) * vv i = 0) :
    ∀ i, p i = 0 := by sorry
