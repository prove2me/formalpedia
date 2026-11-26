-- Prove2me | Theorems.Thm_MohP3_PsurfK_isPrime
-- name    : MohP3.PsurfK_isPrime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:03.708252+00:00
-- url     : https://prove2.me/theorems/df7c92bf-e8fb-4517-8bc9-5a19f90dc4b3
-- title:
--   Moh P3: Psurf K is Prime
-- statement:
--   The Moh P3 construction uses the Psurf K is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L82-L82
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L82-L82

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

theorem MohP3.PsurfK_isPrime : (PsurfK k).IsPrime := by sorry
