-- Prove2me | Theorems.Thm_HatAffineOffsets_puncturedLine_card_eq_allowed
-- name    : HatAffineOffsets.puncturedLine_card_eq_allowed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:18.892466+00:00
-- url     : https://prove2.me/theorems/d1c55411-f3f5-514e-b92f-bd293aeed714
-- title:
--   Hat Affine Offsets: punctured Line card eq allowed
-- statement:
--   The Hat Affine Offsets construction uses the punctured Line card eq allowed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L148-L190
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L148-L190

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.puncturedLine_card_eq_allowed
    {K : Type u} [Field K] [Fintype K]
    (c e : K) :
    (puncturedLine c e).card = (allowedLineParameter c e).card := by sorry
