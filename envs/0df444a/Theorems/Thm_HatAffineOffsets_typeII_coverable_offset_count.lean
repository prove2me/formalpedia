-- Prove2me | Theorems.Thm_HatAffineOffsets_typeII_coverable_offset_count
-- name    : HatAffineOffsets.typeII_coverable_offset_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:33.25095+00:00
-- url     : https://prove2.me/theorems/3da58ad0-b145-42fe-9a83-32a3ffa70da4
-- title:
--   Hat Affine Offsets: type II coverable offset count
-- statement:
--   The Hat Affine Offsets construction uses the type II coverable offset count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L467-L513
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeII.lean#L467-L513

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9

theorem HatAffineOffsets.typeII_coverable_offset_count
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
      F y i = alpha i * (y u - c i * y v) + b i) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      (Fintype.card K) ^ 2 := by sorry
