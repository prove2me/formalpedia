-- Prove2me | Theorems.Thm_Kirkman_kirkman
-- name    : Kirkman.kirkman
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:45:33.998862+00:00
-- url     : https://prove2.me/theorems/706b7f44-3799-4fc1-a06b-b818bd555247
-- title:
--   Kirkman: kirkman
-- statement:
--   **Kirkman (1847).**
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L78-L103
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L78-L103

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman

theorem Kirkman.kirkman (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 := by sorry
