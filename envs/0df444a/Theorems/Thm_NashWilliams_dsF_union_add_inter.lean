-- Prove2me | Theorems.Thm_NashWilliams_dsF_union_add_inter
-- name    : NashWilliams.dsF_union_add_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:01:16.467248+00:00
-- url     : https://prove2.me/theorems/0d0249f8-0166-410b-9e3f-bd579a151a28
-- title:
--   Nash Williams: ds F union add inter
-- statement:
--   The Nash Williams construction uses the ds F union add inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L146-L153
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L146-L153

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.dsF_union_add_inter (s : V) (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    dsF s ends F X + dsF s ends F Y = dsF s ends F (X ∪ Y) + dsF s ends F (X ∩ Y) := by sorry
