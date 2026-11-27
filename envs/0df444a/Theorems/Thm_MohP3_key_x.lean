-- Prove2me | Theorems.Thm_MohP3_key_x
-- name    : MohP3.key_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:46.022496+00:00
-- url     : https://prove2.me/theorems/847b314e-344b-4d6c-afb2-4e2155454902
-- title:
--   Moh P3: key x
-- statement:
--   The Moh P3 construction uses the key x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L186-L188
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L186-L188

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x (i : Fin 8) : (18 : R) * (x * hh i) - ∑ j, iota (QX i j) * hh j ∈ P := by sorry
