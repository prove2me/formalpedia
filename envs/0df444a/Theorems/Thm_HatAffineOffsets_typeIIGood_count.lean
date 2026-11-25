-- Prove2me | Theorems.Thm_HatAffineOffsets_typeIIGood_count
-- name    : HatAffineOffsets.typeIIGood_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:36.199694+00:00
-- url     : https://prove2.me/theorems/3c16bd9a-1d4a-44d3-bd75-17fbab8e82eb
-- title:
--   Hat Affine Offsets: type IIGood count
-- statement:
--   The Hat Affine Offsets construction uses the type IIGood count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L431-L465
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L431-L465

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeIIGood_count
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    (Finset.univ.filter
      (fun d : Fin (Fintype.card K - 1) -> K => TypeIIGood c d)).card =
      (Fintype.card K) ^ 2 := by sorry
