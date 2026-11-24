-- Prove2me | Theorems.Thm_Mader_two_mul_ncard_edgeSet
-- name    : Mader.two_mul_ncard_edgeSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:24.815148+00:00
-- url     : https://prove2.me/theorems/d30e5bf2-5748-4e49-881f-7e456571d0a4
-- title:
--   Mader: two mul ncard edge Set
-- statement:
--   The Mader construction uses the two mul ncard edge Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L110-L114
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L110-L114

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

theorem Mader.two_mul_ncard_edgeSet {W : Type*} [Fintype W] (G' : SimpleGraph W) :
    2 * G'.edgeSet.ncard = ∑ v, G'.degree v := by sorry
