-- Prove2me | Theorems.Thm_NashWilliams_dsF_eq_sum
-- name    : NashWilliams.dsF_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:48.806525+00:00
-- url     : https://prove2.me/theorems/dc814a20-ca4f-4304-9551-fb7915056527
-- title:
--   Nash Williams: ds F eq sum
-- statement:
--   The Nash Williams construction uses the ds F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L61-L64
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L61-L64

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.dsF_eq_sum (s : V) (ends : ι → V × V) (F : Finset ι) (X : Finset V) :
    dsF s ends F X = ∑ l ∈ F, jn s (ends l) X := by sorry
