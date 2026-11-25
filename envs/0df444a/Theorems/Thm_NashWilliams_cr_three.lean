-- Prove2me | Theorems.Thm_NashWilliams_cr_three
-- name    : NashWilliams.cr_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:56.283005+00:00
-- url     : https://prove2.me/theorems/a78b98e5-66d8-5505-b68c-042df05ca74e
-- title:
--   Nash Williams: cr three
-- statement:
--   The three-set uncrossing inequality, edge by edge.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L143-L149
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L143-L149

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cr_three (p : V × V) (A B C : Finset V) :
    cr p ((A \ B) \ C) + cr p ((B \ A) \ C) + cr p ((C \ A) \ B) + cr p (A ∩ B ∩ C) +
      2 * (if (p.1 ∈ A ∩ B ∩ C ∧ p.2 ∉ A ∪ B ∪ C) ∨ (p.2 ∈ A ∩ B ∩ C ∧ p.1 ∉ A ∪ B ∪ C)
        then 1 else 0) ≤ cr p A + cr p B + cr p C := by sorry
