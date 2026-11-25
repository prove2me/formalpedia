-- Prove2me | Theorems.Thm_HatAffineOffsets_typeIID_eq_iff
-- name    : HatAffineOffsets.typeIID_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:12:32.059465+00:00
-- url     : https://prove2.me/theorems/12edea13-5398-46fa-97d0-05d2f5550e77
-- title:
--   Hat Affine Offsets: type IID eq iff
-- statement:
--   The Hat Affine Offsets construction uses the type IID eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L28-L33
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L28-L33

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeIID_eq_iff
    {K : Type u} {I : Type*} [Field K]
    {alpha b x : I -> K} {i : I} {z : K}
    (halpha : alpha i ≠ 0) :
    typeIID alpha b x i = z ↔ alpha i * z + b i = x i := by sorry
