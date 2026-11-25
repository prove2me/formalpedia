-- Prove2me | Theorems.Thm_HatAffineOffsets_nonzeroFinset_card
-- name    : HatAffineOffsets.nonzeroFinset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:10.052748+00:00
-- url     : https://prove2.me/theorems/15836093-d2ac-4003-9c3d-80b320f1f2d9
-- title:
--   Hat Affine Offsets: nonzero Finset card
-- statement:
--   The Hat Affine Offsets construction uses the nonzero Finset card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L192-L196
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L192-L196

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.nonzeroFinset_card
    {K : Type u} [Fintype K] [Zero K] [DecidableEq K] :
    (nonzeroFinset K).card = Fintype.card K - 1 := by sorry
