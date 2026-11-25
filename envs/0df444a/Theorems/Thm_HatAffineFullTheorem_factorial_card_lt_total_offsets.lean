-- Prove2me | Theorems.Thm_HatAffineFullTheorem_factorial_card_lt_total_offsets
-- name    : HatAffineFullTheorem.factorial_card_lt_total_offsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:51.828794+00:00
-- url     : https://prove2.me/theorems/113d27ef-67ae-462b-b256-6157bfb367e8
-- title:
--   Hat Affine Full Theorem: factorial card lt total offsets
-- statement:
--   The Hat Affine Full Theorem construction uses the factorial card lt total offsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L37-L53
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineFullTheorem/GeneralNoGo.lean#L37-L53

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11

theorem HatAffineFullTheorem.factorial_card_lt_total_offsets
    (q : Nat) (hq : 4 ≤ q) :
    Nat.factorial q < q ^ (q - 1) := by sorry
