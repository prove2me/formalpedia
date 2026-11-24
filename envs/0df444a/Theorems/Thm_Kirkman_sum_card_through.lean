-- Prove2me | Theorems.Thm_Kirkman_sum_card_through
-- name    : Kirkman.sum_card_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:45:27.767108+00:00
-- url     : https://prove2.me/theorems/c11eccb0-0648-4b1c-a57e-1c14c96c5d8a
-- title:
--   Kirkman: sum card through
-- statement:
--   The double count `∑ₓ #{T ∋ x} = 3 #𝒯`.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L67-L75
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L67-L75

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman

theorem Kirkman.sum_card_through {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) :
    ∑ x : Fin v, #(𝒯.filter (fun T => x ∈ T)) = 3 * #𝒯 := by sorry
