-- Prove2me | Theorems.Thm_HatAffineOffsets_puncturedPairs_card
-- name    : HatAffineOffsets.puncturedPairs_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:10.360234+00:00
-- url     : https://prove2.me/theorems/cc6b7e0f-6b77-4998-b7f8-9311276e4a1b
-- title:
--   Hat Affine Offsets: punctured Pairs card
-- statement:
--   The Hat Affine Offsets construction uses the punctured Pairs card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L198-L207
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L198-L207

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.puncturedPairs_card
    {K : Type u} [Fintype K] [Zero K] [DecidableEq K] :
    (puncturedPairs K).card = (Fintype.card K - 1) ^ 2 := by sorry
