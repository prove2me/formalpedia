-- Prove2me | Theorems.Thm_HatAffineOffsets_genericTypeII_coverable_offset_count
-- name    : HatAffineOffsets.genericTypeII_coverable_offset_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:06.232182+00:00
-- url     : https://prove2.me/theorems/f1c49ee9-bab0-5186-a4ce-8c3e665f69dd
-- title:
--   Hat Affine Offsets: generic Type II coverable offset count
-- statement:
--   The Hat Affine Offsets construction uses the generic Type II coverable offset count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L533-L552
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L533-L552

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.genericTypeII_coverable_offset_count
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (A : Fin (Fintype.card K - 1) -> Fin m -> K)
    (lambda : Fin m -> K)
    (b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (hII : HatAffineFactorAlignment.GenericTypeII A lambda)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      (Fintype.card K) ^ 2 := by sorry
