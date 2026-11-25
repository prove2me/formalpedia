-- Prove2me | Theorems.Thm_NashWilliams_cutF_pair_le
-- name    : NashWilliams.cutF_pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:14.694553+00:00
-- url     : https://prove2.me/theorems/cc26de3c-5ec8-5104-a71c-2f4866b3e9d9
-- title:
--   Nash Williams: cut F pair le
-- statement:
--   If no active edge lies inside `X`, then the cut of `X` is at least the sum of the cuts of two
--   distinct vertices of `X`.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L131-L140
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L131-L140

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_pair_le {ends : ι → V × V} {F : Finset ι} {X : Finset V} {x y : V} (hxy : x ≠ y)
    (hx : x ∈ X) (hy : y ∈ X) (hno : ∀ i ∈ F, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)) :
    cutF ends F {x} + cutF ends F {y} ≤ cutF ends F X := by sorry
