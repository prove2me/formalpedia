-- Prove2me | Theorems.Thm_HatAffineOffsets_puncturedLine_card
-- name    : HatAffineOffsets.puncturedLine_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:31.366307+00:00
-- url     : https://prove2.me/theorems/8e81adca-b497-5548-8c38-255e0bc14a83
-- title:
--   Hat Affine Offsets: punctured Line card
-- statement:
--   The Hat Affine Offsets construction uses the punctured Line card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L209-L258
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L209-L258

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.puncturedLine_card
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c e : K) (hc : c ≠ 0) :
    (puncturedLine c e).card =
      if e = 0 then Fintype.card K - 1 else Fintype.card K - 2 := by sorry
