-- Prove2me | Theorems.Thm_HatAffineOffsets_typeII_offsetCoverable_iff_good
-- name    : HatAffineOffsets.typeII_offsetCoverable_iff_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:20.136499+00:00
-- url     : https://prove2.me/theorems/b0593c2e-dd96-466f-a3ed-223801de80c1
-- title:
--   Hat Affine Offsets: type II offset Coverable iff good
-- statement:
--   The Hat Affine Offsets construction uses the type II offset Coverable iff good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L373-L389
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L373-L389

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeII_offsetCoverable_iff_good
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (u v : Fin m)
    (alpha c b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (huv : u ≠ v)
    (halpha : forall i, alpha i ≠ 0)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z)
    (hrealizeII : forall y i,
      F y i = alpha i * (y u - c i * y v) + b i)
    (x : Fin (Fintype.card K - 1) -> K) :
    OffsetCoverable F x ↔ TypeIIGood c (typeIID alpha b x) := by sorry
