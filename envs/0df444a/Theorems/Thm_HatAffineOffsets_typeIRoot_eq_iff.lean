-- Prove2me | Theorems.Thm_HatAffineOffsets_typeIRoot_eq_iff
-- name    : HatAffineOffsets.typeIRoot_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:10:00.90212+00:00
-- url     : https://prove2.me/theorems/566461e8-d1a5-4a3c-b086-918e61be6817
-- title:
--   Hat Affine Offsets: type IRoot eq iff
-- statement:
--   The Hat Affine Offsets construction uses the type IRoot eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L39-L54
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L39-L54

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.typeIRoot_eq_iff
    {K : Type u} [Field K]
    {alpha b x y : K} (halpha : alpha ≠ 0) :
    (x - b) / alpha = y <-> alpha * y + b = x := by sorry
