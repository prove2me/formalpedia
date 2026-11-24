-- Prove2me | Theorems.Thm_Kirkman_z3_pred_succ
-- name    : Kirkman.z3_pred_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:42:00.247144+00:00
-- url     : https://prove2.me/theorems/659193cb-6201-4f3f-aea7-a8d97e2a33d8
-- title:
--   Kirkman: z3 pred succ
-- statement:
--   The Kirkman construction uses the z3 pred succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Constructions.lean#L46-L46
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Constructions.lean#L46-L46

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Definitions.Def_KirkmanLib_Constructions
set_option autoImplicit true
@[expose] public section
public section
open Kirkman

theorem Kirkman.z3_pred_succ (i : ZMod 3) : i - 1 + 1 = i := by sorry
