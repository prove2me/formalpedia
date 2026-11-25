-- Prove2me | Theorems.Thm_NashWilliams_req_erase_of_req
-- name    : NashWilliams.req_erase_of_req
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:36.323503+00:00
-- url     : https://prove2.me/theorems/d4663ebb-4ccd-5d54-8909-010293a63c4d
-- title:
--   Nash Williams: req erase of req
-- statement:
--   The Nash Williams construction uses the req erase of req property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L165-L172
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L165-L172

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]

theorem NashWilliams.req_erase_of_req {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) (s : V) : Req K (T.erase s) ends F := by sorry
