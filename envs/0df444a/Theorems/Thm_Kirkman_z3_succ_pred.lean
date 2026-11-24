-- Prove2me | Theorems.Thm_Kirkman_z3_succ_pred
-- name    : Kirkman.z3_succ_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:42:09.539087+00:00
-- url     : https://prove2.me/theorems/b96eb336-53f4-4a93-b734-73e020c57a04
-- title:
--   Kirkman: z3 succ pred
-- statement:
--   The Kirkman construction uses the z3 succ pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Constructions.lean#L47-L47
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Constructions.lean#L47-L47

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Definitions.Def_KirkmanLib_Constructions
set_option autoImplicit true
@[expose] public section
public section
open Kirkman

theorem Kirkman.z3_succ_pred (i : ZMod 3) : i + 1 - 1 = i := by sorry
