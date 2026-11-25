-- Prove2me | Theorems.Thm_HatAffineOffsets_sum_typeII_row
-- name    : HatAffineOffsets.sum_typeII_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:05.938534+00:00
-- url     : https://prove2.me/theorems/e39ef3c6-a26b-42ac-a35a-96a89b05dace
-- title:
--   Hat Affine Offsets: sum type II row
-- statement:
--   The Hat Affine Offsets construction uses the sum type II row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L515-L531
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L515-L531

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.sum_typeII_row
    {K : Type u} [Field K] {m : Nat}
    (u v : Fin m) (huv : u ≠ v) (alpha c : K) (y : Fin m -> K) :
    (∑ j, (if j = u then alpha else if j = v then -alpha * c else 0) * y j) =
      alpha * (y u - c * y v) := by sorry
