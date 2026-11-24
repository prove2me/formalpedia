-- Prove2me | Theorems.Thm_Kirkman_boseQ_idem
-- name    : Kirkman.boseQ_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:56.205688+00:00
-- url     : https://prove2.me/theorems/69e754c0-46ba-40fd-bb1f-7b30a0c8fa22
-- title:
--   Kirkman: bose Q idem
-- statement:
--   The Kirkman construction uses the bose Q idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Instances.lean#L51-L53
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Instances.lean#L51-L53

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Constructions
public import Definitions.Def_KirkmanLib_Instances
set_option autoImplicit true
@[expose] public section
public section
open Kirkman
variable {n : ℕ} (hn : n % 2 = 1)

theorem Kirkman.boseQ_idem (x : ZMod n) : (boseQ hn).L x x = x := by sorry
