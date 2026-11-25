-- Prove2me | Theorems.Thm_HatAffineOffsets_typeI_offsetCoverable_iff_injective
-- name    : HatAffineOffsets.typeI_offsetCoverable_iff_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:38.168029+00:00
-- url     : https://prove2.me/theorems/8999ad73-5412-54c5-a4e5-9274e170d4d2
-- title:
--   Hat Affine Offsets: type I offset Coverable iff injective
-- statement:
--   The Hat Affine Offsets construction uses the type I offset Coverable iff injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L112-L208
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L112-L208

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.typeI_offsetCoverable_iff_injective
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (r : Fin m)
    (alpha b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (halpha : forall i, alpha i ≠ 0)
    (hrealizeI : forall y i, F y i = alpha i * y r + b i)
    (x : Fin (Fintype.card K - 1) -> K) :
    OffsetCoverable F x <-> Function.Injective (typeIRoot alpha b x) := by sorry
