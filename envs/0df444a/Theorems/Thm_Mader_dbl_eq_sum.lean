-- Prove2me | Theorems.Thm_Mader_dbl_eq_sum
-- name    : Mader.dbl_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:39.705976+00:00
-- url     : https://prove2.me/theorems/e1564b00-7cf6-443b-9a5c-4f4e4a57f111
-- title:
--   Mader: dbl eq sum
-- statement:
--   The Mader construction uses the dbl eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L37-L42
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L37-L42

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

theorem Mader.dbl_eq_sum (S : Finset V) : dbl G S = ∑ v ∈ S, ndeg G S v := by sorry
