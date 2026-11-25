-- Prove2me | Theorems.Thm_HatAffineOffsets_typeII_cross_iff_good
-- name    : HatAffineOffsets.typeII_cross_iff_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:40.984499+00:00
-- url     : https://prove2.me/theorems/5681a8f4-a500-59a7-80c3-6f4787a33e76
-- title:
--   Hat Affine Offsets: type II cross iff good
-- statement:
--   The Hat Affine Offsets construction uses the type II cross iff good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L260-L371
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L260-L371

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeII_cross_iff_good
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c d : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    TypeIICross c d ↔ TypeIIGood c d := by sorry
