-- Prove2me | Theorems.Thm_NashWilliams_exists_smaller_tight
-- name    : NashWilliams.exists_smaller_tight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:44.515897+00:00
-- url     : https://prove2.me/theorems/94153d41-9e44-4f1a-b6d6-487d541e804c
-- title:
--   Nash Williams: exists smaller tight
-- statement:
--   Uncrossing step: a tight set `X` containing `a` and `b`, and a tight set `Y` containing `a`
--   but not `b`, yield a strictly smaller tight set.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L47-L88
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L47-L88

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]

theorem NashWilliams.exists_smaller_tight {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {X Y : Finset V} (hX : Tight K T ends F X) (hY : Tight K T ends F Y)
    {a b : V} (haX : a ∈ X) (hbX : b ∈ X) (haY : a ∈ Y) (hbY : b ∉ Y) :
    ∃ Z, Tight K T ends F Z ∧ Z.card < X.card := by sorry
