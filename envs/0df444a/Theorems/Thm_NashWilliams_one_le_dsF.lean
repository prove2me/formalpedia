-- Prove2me | Theorems.Thm_NashWilliams_one_le_dsF
-- name    : NashWilliams.one_le_dsF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:06:53.983165+00:00
-- url     : https://prove2.me/theorems/953b4116-d2a7-4ec2-a111-25c6c18a33f1
-- title:
--   Nash Williams: one le ds F
-- statement:
--   The Nash Williams construction uses the one le ds F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L173-L177
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L173-L177

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.one_le_dsF {s u : V} {ends : ι → V × V} {F : Finset ι} {i : ι} (hi : i ∈ F)
    (hJ : Joins s u (ends i)) {X : Finset V} (hu : u ∈ X) : 1 ≤ dsF s ends F X := by sorry
