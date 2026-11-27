-- Prove2me | Theorems.Thm_MohP3_H1_mem_P
-- name    : MohP3.H1_mem_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:14:17.753735+00:00
-- url     : https://prove2.me/theorems/4f03b417-fbc4-48de-a8b6-d72ca3d4a59d
-- title:
--   Moh P3: H1 mem P
-- statement:
--   The Moh P3 construction uses the H1 mem P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Certificate.lean#L50-L50
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Certificate.lean#L50-L50

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H1_mem_P

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.H1_mem_P : H1 ∈ P := by sorry
