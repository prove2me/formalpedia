-- Prove2me | Theorems.Thm_Mader_dbl_le
-- name    : Mader.dbl_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:32.842208+00:00
-- url     : https://prove2.me/theorems/6039a85a-48d9-4b90-9d5b-0f32a4c96b3f
-- title:
--   Mader: dbl le
-- statement:
--   The Mader construction uses the dbl le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L63-L67
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L63-L67

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)

theorem Mader.dbl_le (S : Finset V) : dbl G S ≤ S.card * (S.card - 1) := by sorry
