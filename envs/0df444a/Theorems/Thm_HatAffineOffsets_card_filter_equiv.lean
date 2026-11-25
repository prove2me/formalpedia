-- Prove2me | Theorems.Thm_HatAffineOffsets_card_filter_equiv
-- name    : HatAffineOffsets.card_filter_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:16:35.40775+00:00
-- url     : https://prove2.me/theorems/a0cba077-7343-441b-8f1d-2b3b2cbcc67b
-- title:
--   Hat Affine Offsets: card filter equiv
-- statement:
--   The Hat Affine Offsets construction uses the card filter equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L56-L69
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineOffsets/TypeI.lean#L56-L69

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10

theorem HatAffineOffsets.card_filter_equiv
    {X : Type v} {Y : Type w} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : Y -> Prop) :
    (Finset.univ.filter (fun x => p (e x))).card =
      (Finset.univ.filter p).card := by sorry
