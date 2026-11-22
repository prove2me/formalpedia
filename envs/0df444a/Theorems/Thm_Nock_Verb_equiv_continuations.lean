-- Prove2me | Theorems.Thm_Nock_Verb_equiv_continuations
-- name    : Nock.Verb.equiv_continuations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:36.018794+00:00
-- url     : https://prove2.me/theorems/d40dd07b-4622-4aa6-89c6-3271e3520e21
-- title:
--   Verb: equiv continuations
-- statement:
--   **`lemma:equiv_continuations`** (`main.tex:1150–1153`).
--       `NockVM^Λ ≡ FiniteTransitions^Λ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L142-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L142-L148

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.equiv_continuations (F : Verb) : Finite F ↔ FiniteTransition F := by sorry
