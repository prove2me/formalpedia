-- Prove2me | Theorems.Thm_HatAffineFullTheorem_affine_factor_alignment_of_extends
-- name    : HatAffineFullTheorem.affine_factor_alignment_of_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:20.27681+00:00
-- url     : https://prove2.me/theorems/5708003c-4c59-4e08-8004-4fc86a705d5a
-- title:
--   Hat Affine Full Theorem: affine factor alignment of extends
-- statement:
--   The Hat Affine Full Theorem construction uses the affine factor alignment of extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/LeadingClassification.lean#L82-L189
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/LeadingClassification.lean#L82-L189

import Definitions.Def_HatAffineGenericCore_G2
import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineFullTheorem_LeadingClassification
set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore

theorem HatAffineFullTheorem.affine_factor_alignment_of_extends
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (b : Fin (Fintype.card K - 1) → K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F)
    (hext : HatAffineGeneral.Extends F) :
    ∃ lambda : Fin m → K,
      HatAffineFactorAlignment.GenericTypeI A lambda ∨
      HatAffineFactorAlignment.GenericTypeII A lambda := by sorry
