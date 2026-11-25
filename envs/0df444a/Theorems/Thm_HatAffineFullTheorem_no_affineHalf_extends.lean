-- Prove2me | Theorems.Thm_HatAffineFullTheorem_no_affineHalf_extends
-- name    : HatAffineFullTheorem.no_affineHalf_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:39.507105+00:00
-- url     : https://prove2.me/theorems/d874c1c2-4bcc-50d2-851c-21e4c1d2ef5a
-- title:
--   Hat Affine Full Theorem: no affine Half extends
-- statement:
--   The Hat Affine Full Theorem construction uses the no affine Half extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L88-L97
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L88-L97

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11

theorem HatAffineFullTheorem.no_affineHalf_extends
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hF : HatAffineGeneral.AffineHalf F) :
    ¬ HatAffineGeneral.Extends F := by sorry
