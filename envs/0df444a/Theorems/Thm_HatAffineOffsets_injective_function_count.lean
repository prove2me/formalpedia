-- Prove2me | Theorems.Thm_HatAffineOffsets_injective_function_count
-- name    : HatAffineOffsets.injective_function_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:11:42.146162+00:00
-- url     : https://prove2.me/theorems/cefd3531-0436-42e8-84c9-dae460cbab92
-- title:
--   Hat Affine Offsets: injective function count
-- statement:
--   The Hat Affine Offsets construction uses the injective function count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L71-L110
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L71-L110

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.injective_function_count
    {K : Type u} [Fintype K]
    (hq : 1 <= Fintype.card K) :
    (Finset.univ.filter
      (fun f : Fin (Fintype.card K - 1) -> K =>
        Function.Injective f)).card =
      Nat.factorial (Fintype.card K) := by sorry
