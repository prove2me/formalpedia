-- Prove2me | Theorems.Thm_Kirkman_IsSTSOn_map
-- name    : Kirkman.IsSTSOn.map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:18.428854+00:00
-- url     : https://prove2.me/theorems/9347f553-73da-45f5-85be-af6338fce35d
-- title:
--   Is STSOn: map
-- statement:
--   A Steiner triple system transports along a bijection.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L116-L139
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L116-L139

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}

theorem Kirkman.IsSTSOn.map [DecidableEq P] {Q : Type*} [DecidableEq Q] {𝒯 : Finset (Finset P)} (h :
    IsSTSOn 𝒯)
    (e : P ≃ Q) : IsSTSOn (𝒯.map ⟨fun T => T.map e.toEmbedding, map_injective _⟩) := by sorry
