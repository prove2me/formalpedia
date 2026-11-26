-- Prove2me | Theorems.Thm_MohP3_ntd_vv
-- name    : MohP3.ntd_vv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:41.76722+00:00
-- url     : https://prove2.me/theorems/d6c0aa63-bee2-41c8-8d1b-ba9416064ad4
-- title:
--   Moh P3: ntd vv
-- statement:
--   The Moh P3 construction uses the ntd vv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L63-L72
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L63-L72

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.ntd_vv (i : Fin 8) : (vv i).natTrailingDegree = oo i := by sorry
