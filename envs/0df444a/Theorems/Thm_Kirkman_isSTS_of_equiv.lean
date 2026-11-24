-- Prove2me | Theorems.Thm_Kirkman_isSTS_of_equiv
-- name    : Kirkman.isSTS_of_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:45:33.310694+00:00
-- url     : https://prove2.me/theorems/6ca99ae8-9ae9-47c2-8f20-e6151ac29167
-- title:
--   Kirkman: is STS of equiv
-- statement:
--   The Kirkman construction uses the is STS of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L33-L36
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/Kirkman.lean#L33-L36

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman

theorem Kirkman.isSTS_of_equiv {P : Type*} [Fintype P] {v : ℕ} (S : SteinerOp P)
    (hP : Fintype.card P = v) : ∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯 := by sorry
