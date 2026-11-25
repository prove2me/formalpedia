-- Prove2me | Theorems.Thm_HatAffineOffsets_genericTypeI_coverable_offset_count
-- name    : HatAffineOffsets.genericTypeI_coverable_offset_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:51.489341+00:00
-- url     : https://prove2.me/theorems/1631790f-a6a7-50f6-8bf8-78b777c6418c
-- title:
--   Hat Affine Offsets: generic Type I coverable offset count
-- statement:
--   The Hat Affine Offsets construction uses the generic Type I coverable offset count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L256-L274
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L256-L274

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.genericTypeI_coverable_offset_count
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (A : Fin (Fintype.card K - 1) -> Fin m -> K)
    (lambda : Fin m -> K)
    (b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (hI : HatAffineFactorAlignment.GenericTypeI A lambda)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      Nat.factorial (Fintype.card K) := by sorry
