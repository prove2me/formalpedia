-- Prove2me | Theorems.Thm_HatAffineConstantRows_no_constant_row_of_extends_affine
-- name    : HatAffineConstantRows.no_constant_row_of_extends_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:27.241408+00:00
-- url     : https://prove2.me/theorems/42834465-30ef-49ee-adb8-5b3a78ced9ee
-- title:
--   Hat Affine Constant Rows: no constant row of extends affine
-- statement:
--   The Hat Affine Constant Rows construction uses the no constant row of extends affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L232-L273
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/ConstantRows.lean#L232-L273

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial

theorem HatAffineConstantRows.no_constant_row_of_extends_affine
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (b : Fin (Fintype.card K - 1) → K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hrealize : AffineRealizes A b F)
    (hext : HatAffineGeneral.Extends F) :
    ∀ i, A i ≠ 0 := by sorry
