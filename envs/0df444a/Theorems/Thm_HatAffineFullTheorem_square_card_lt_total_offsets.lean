-- Prove2me | Theorems.Thm_HatAffineFullTheorem_square_card_lt_total_offsets
-- name    : HatAffineFullTheorem.square_card_lt_total_offsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:50.549561+00:00
-- url     : https://prove2.me/theorems/5bcce806-5c42-4200-b405-4dba1341bb3f
-- title:
--   Hat Affine Full Theorem: square card lt total offsets
-- statement:
--   The Hat Affine Full Theorem construction uses the square card lt total offsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L55-L58
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L55-L58

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11

theorem HatAffineFullTheorem.square_card_lt_total_offsets
    (q : Nat) (hq : 4 ≤ q) :
    q ^ 2 < q ^ (q - 1) := by sorry
