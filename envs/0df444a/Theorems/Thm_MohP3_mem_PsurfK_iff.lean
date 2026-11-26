-- Prove2me | Theorems.Thm_MohP3_mem_PsurfK_iff
-- name    : MohP3.mem_PsurfK_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:16.379136+00:00
-- url     : https://prove2.me/theorems/b58a0b0c-dd48-5a71-8054-df1c9f28137d
-- title:
--   Moh P3: mem Psurf K iff
-- statement:
--   The Moh P3 construction uses the mem Psurf K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L79-L79
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L79-L79

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.mem_PsurfK_iff {g : Rk k} : g ∈ PsurfK k ↔ sigmaK k g = 0 := by sorry
