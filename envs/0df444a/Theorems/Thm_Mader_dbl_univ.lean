-- Prove2me | Theorems.Thm_Mader_dbl_univ
-- name    : Mader.dbl_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:37.119829+00:00
-- url     : https://prove2.me/theorems/7ee59a81-8446-44e3-a475-1c15ca3a8217
-- title:
--   Mader: dbl univ
-- statement:
--   The Mader construction uses the dbl univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L117-L122
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L117-L122

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

theorem Mader.dbl_univ [Fintype V] : dbl G univ = 2 * G.edgeSet.ncard := by sorry
