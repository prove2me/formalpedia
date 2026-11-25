-- Prove2me | Theorems.Thm_HatAffineOffsets_typeIIParam_injective
-- name    : HatAffineOffsets.typeIIParam_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:41.590963+00:00
-- url     : https://prove2.me/theorems/16e7c9b5-d1bb-54e9-ab95-ec86851778ec
-- title:
--   Hat Affine Offsets: type IIParam injective
-- statement:
--   The Hat Affine Offsets construction uses the type IIParam injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L396-L429
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L396-L429

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeIIParam_injective
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    Function.Injective (typeIIParam c) := by sorry
