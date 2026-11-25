-- Prove2me | Theorems.Thm_HatAffineOffsets_nonzero_subtype_card
-- name    : HatAffineOffsets.nonzero_subtype_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:16.2608+00:00
-- url     : https://prove2.me/theorems/4d22dcb2-eef4-5e4d-8926-148da2f484c2
-- title:
--   Hat Affine Offsets: nonzero subtype card
-- statement:
--   The Hat Affine Offsets construction uses the nonzero subtype card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L93-L103
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L93-L103

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.nonzero_subtype_card
    {K : Type u} [Fintype K] [Zero K] [DecidableEq K] :
    Fintype.card {z : K // z ≠ 0} = Fintype.card K - 1 := by sorry
