-- Prove2me | Theorems.Thm_HatAffineOffsets_typeII_slope_injective
-- name    : HatAffineOffsets.typeII_slope_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:31.264291+00:00
-- url     : https://prove2.me/theorems/acc4c136-1695-449c-b5b5-f28b72ecaddb
-- title:
--   Hat Affine Offsets: type II slope injective
-- statement:
--   The Hat Affine Offsets construction uses the type II slope injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L105-L128
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L105-L128

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeII_slope_injective
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    Function.Injective c := by sorry
