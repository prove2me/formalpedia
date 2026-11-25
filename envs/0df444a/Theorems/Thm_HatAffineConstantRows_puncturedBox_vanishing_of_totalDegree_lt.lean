-- Prove2me | Theorems.Thm_HatAffineConstantRows_puncturedBox_vanishing_of_totalDegree_lt
-- name    : HatAffineConstantRows.puncturedBox_vanishing_of_totalDegree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:09:39.788798+00:00
-- url     : https://prove2.me/theorems/d5943fc3-095e-4d9f-b623-6c18df4f8f0c
-- title:
--   Hat Affine Constant Rows: punctured Box vanishing of total Degree lt
-- statement:
--   The Hat Affine Constant Rows construction uses the punctured Box vanishing of total Degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/LowDegreeBox.lean#L86-L133
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineConstantRows/LowDegreeBox.lean#L86-L133

import Definitions.Def_HatAffineGenericCore_G2
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u
open Finset
open MvPolynomial

theorem HatAffineConstantRows.puncturedBox_vanishing_of_totalDegree_lt
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (g : Fin m → K)
    (P : MvPolynomial (Fin m) K)
    (hdeg : P.totalDegree < Fintype.card K - 1)
    (hvanish :
      ∀ y : Fin m → K,
        (∀ j, y j ≠ g j) →
        MvPolynomial.eval y P = 0) :
    P = 0 := by sorry
