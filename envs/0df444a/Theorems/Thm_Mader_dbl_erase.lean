-- Prove2me | Theorems.Thm_Mader_dbl_erase
-- name    : Mader.dbl_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:33.15541+00:00
-- url     : https://prove2.me/theorems/25eb8097-1e59-468b-b5f5-cb21885cf7a9
-- title:
--   Mader: dbl erase
-- statement:
--   The Mader construction uses the dbl erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L70-L94
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean#L70-L94

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

theorem Mader.dbl_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    dbl G S ≤ dbl G (S.erase v) + 2 * ndeg G S v := by sorry
