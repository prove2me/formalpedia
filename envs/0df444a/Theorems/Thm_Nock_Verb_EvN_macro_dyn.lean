-- Prove2me | Theorems.Thm_Nock_Verb_EvN_macro_dyn
-- name    : Nock.Verb.EvN_macro_dyn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:42.873099+00:00
-- url     : https://prove2.me/theorems/85de3793-82c9-4c98-bbdf-70bed5c45c5f
-- title:
--   Verb: Ev N macro dyn
-- statement:
--   **The dynamic-hint macro `*[a 8 c [7 [0 3] d]]` has the same big-step value as OP₁₁**:
--       evaluate the clue `c`, keep the original subject `a` via `/[3]`, then run the body `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L673-L695
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L673-L695

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.EvN_macro_dyn {subj clue body x} :
    Ev subj (.cell (.atom 8)
        (.cell clue (.cell (.atom 7) (.cell (.cell (.atom 0) (.atom 3)) body)))) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by sorry
