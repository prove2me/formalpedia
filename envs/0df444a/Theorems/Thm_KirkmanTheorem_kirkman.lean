-- Prove2me | Theorems.Thm_KirkmanTheorem_kirkman
-- name    : KirkmanTheorem.kirkman
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:54:16.346864+00:00
-- url     : https://prove2.me/theorems/8804213f-3d58-4040-bf77-ebc1c87fea35
-- title:
--   Kirkman Theorem: kirkman
-- statement:
--   **Kirkman (1847).**
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/Solution.lean#L34-L36
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/Solution.lean#L34-L36

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Kirkman
public import Definitions.Def_KirkmanLib_Solution
public import Theorems.Thm_Kirkman_kirkman

set_option autoImplicit true
@[expose] public section
public section
open Finset
open KirkmanTheorem

theorem KirkmanTheorem.kirkman (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 := by sorry
