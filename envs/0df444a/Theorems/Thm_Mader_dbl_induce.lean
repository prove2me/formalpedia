-- Prove2me | Theorems.Thm_Mader_dbl_induce
-- name    : Mader.dbl_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:33.231039+00:00
-- url     : https://prove2.me/theorems/ec1a46af-babc-40a5-9543-04e2b8649e60
-- title:
--   Mader: dbl induce
-- statement:
--   The Mader construction uses the dbl induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L125-L140
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L125-L140

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
open Classical

theorem Mader.dbl_induce (S : Finset V) :
    dbl G S = 2 * (G.induce (S : Set V)).edgeSet.ncard := by sorry
