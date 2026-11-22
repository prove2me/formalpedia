-- Prove2me | Theorems.Thm_GJKKL_mem_matchingsOfSize
-- name    : GJKKL.mem_matchingsOfSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:51.466709+00:00
-- url     : https://prove2.me/theorems/6d6be143-67b9-429b-9ea8-419595ee4966
-- title:
--   GJKKL: mem matchings Of Size
-- statement:
--   The GJKKL construction uses the mem matchings Of Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Statement.lean#L48-L51
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Statement.lean#L48-L51

module
public import Definitions.Def_RequestProject_Pseudorandom_Defs
public import Definitions.Def_GJKKL_Statement
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [DecidableEq V]

theorem GJKKL.mem_matchingsOfSize {H M : Finset (Finset V)} {m : ℕ} :
    M ∈ matchingsOfSize H m ↔ M ⊆ H ∧ IsMatching M ∧ M.card = m := by sorry
