-- Prove2me | Theorems.Thm_HatAffineFullTheorem_all_offsetCoverable_count_of_extends
-- name    : HatAffineFullTheorem.all_offsetCoverable_count_of_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:51.010798+00:00
-- url     : https://prove2.me/theorems/87a8a58b-1e2a-45aa-a29f-8faaeabee571
-- title:
--   Hat Affine Full Theorem: all offset Coverable count of extends
-- statement:
--   The Hat Affine Full Theorem construction uses the all offset Coverable count of extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L14-L35
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L14-L35

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11

theorem HatAffineFullTheorem.all_offsetCoverable_count_of_extends
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (F : (Fin m → K) → Fin (Fintype.card K - 1) → K)
    (hext : HatAffineGeneral.Extends F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) → K =>
        HatAffineOffsets.OffsetCoverable F x)).card =
      (Fintype.card K) ^ (Fintype.card K - 1) := by sorry
