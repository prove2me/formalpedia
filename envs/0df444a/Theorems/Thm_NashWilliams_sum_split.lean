-- Prove2me | Theorems.Thm_NashWilliams_sum_split
-- name    : NashWilliams.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:01.69626+00:00
-- url     : https://prove2.me/theorems/1947ed6a-76c8-41bd-9976-9bff6b8f5180
-- title:
--   Nash Williams: sum split
-- statement:
--   Bookkeeping for the replacement of the edges `i`, `j` by a single edge stored at `i`.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L67-L78
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L67-L78

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.sum_split [DecidableEq ι] {f f1 : ι → ℕ} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (hf : ∀ l ∈ F, l ≠ i → l ≠ j → f1 l = f l) :
    ∑ l ∈ F, f l + f1 i = ∑ l ∈ F.erase j, f1 l + f i + f j := by sorry
