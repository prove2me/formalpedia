-- Prove2me | Theorems.Thm_Kirkman_two_mul_card_through
-- name    : Kirkman.two_mul_card_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:45:30.19027+00:00
-- url     : https://prove2.me/theorems/d88c9bb0-17ea-4e5b-b860-bacf59120b44
-- title:
--   Kirkman: two mul card through
-- statement:
--   Every point lies in `(v - 1) / 2` triples.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L39-L64
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L39-L64

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman

theorem Kirkman.two_mul_card_through {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) (x : Fin v) :
    2 * #(𝒯.filter (fun T => x ∈ T)) = v - 1 := by sorry
