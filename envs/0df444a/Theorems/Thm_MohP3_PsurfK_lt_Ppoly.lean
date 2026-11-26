-- Prove2me | Theorems.Thm_MohP3_PsurfK_lt_Ppoly
-- name    : MohP3.PsurfK_lt_Ppoly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:07.743486+00:00
-- url     : https://prove2.me/theorems/727e24d4-b2c8-58ee-8309-a02c46c2eead
-- title:
--   Moh P3: Psurf K lt Ppoly
-- statement:
--   The Moh P3 construction uses the Psurf K lt Ppoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L117-L119
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L117-L119

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

theorem MohP3.PsurfK_lt_Ppoly : PsurfK k < Ppoly k := by sorry
