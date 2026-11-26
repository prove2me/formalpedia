-- Prove2me | Theorems.Thm_MohP3_mem_of_nsmul_mem
-- name    : MohP3.mem_of_nsmul_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:45:46.574714+00:00
-- url     : https://prove2.me/theorems/36383bd2-bc65-4b97-bdf9-7a1e5e743cc9
-- title:
--   Moh P3: mem of nsmul mem
-- statement:
--   A nonzero natural number is a unit of `ℚ`, hence may be cancelled from an
--   ideal membership.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Defs.lean#L96-L101
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Defs.lean#L96-L101

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.mem_of_nsmul_mem {I : Ideal R} {n : ℕ} (hn : n ≠ 0) {g : R}
    (h : (n : R) * g ∈ I) : g ∈ I := by sorry
