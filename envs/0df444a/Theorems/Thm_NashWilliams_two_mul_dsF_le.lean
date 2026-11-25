-- Prove2me | Theorems.Thm_NashWilliams_two_mul_dsF_le
-- name    : NashWilliams.two_mul_dsF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:00:46.174306+00:00
-- url     : https://prove2.me/theorems/c7e27e12-16cb-5bf2-ae83-b2102e120060
-- title:
--   Nash Williams: two mul ds F le
-- statement:
--   A dangerous set receives at most half of the edges at `s` (the degree of `s` being even).
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L118-L144
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L118-L144

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.two_mul_dsF_le {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F) (heven : Even (cutF ends F {s}))
    {X : Finset V} (hXT : X ⊆ T.erase s) (hXne : X.Nonempty) (hXT' : X ≠ T.erase s)
    (hXc : cutF ends F X ≤ K + 1) : 2 * dsF s ends F X ≤ cutF ends F {s} := by sorry
