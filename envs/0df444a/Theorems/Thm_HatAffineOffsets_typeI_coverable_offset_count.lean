-- Prove2me | Theorems.Thm_HatAffineOffsets_typeI_coverable_offset_count
-- name    : HatAffineOffsets.typeI_coverable_offset_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:43.054897+00:00
-- url     : https://prove2.me/theorems/b27656a6-934e-5b0e-9f8b-2c88a1df6117
-- title:
--   Hat Affine Offsets: type I coverable offset count
-- statement:
--   The Hat Affine Offsets construction uses the type I coverable offset count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L210-L254
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L210-L254

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.typeI_coverable_offset_count
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (r : Fin m)
    (alpha b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (halpha : forall i, alpha i ≠ 0)
    (hrealizeI : forall y i, F y i = alpha i * y r + b i) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      Nat.factorial (Fintype.card K) := by sorry
