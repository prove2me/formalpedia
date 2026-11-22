-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op11_dyn
-- name    : Nock.Verb.EvN_op11_dyn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:33.595253+00:00
-- url     : https://prove2.me/theorems/aaef2aed-ea2f-496f-8ef8-e6e6f4bab554
-- title:
--   Verb: Ev N op11 dyn
-- statement:
--   **`evalN` OP₁₁ dynamic clause**, as a big-step equivalence: `*[a 11 [t c] d]` succeeds iff
--       the clue `c` converges and the body `d` yields the result (the clue value is discarded).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L645-L659
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L645-L659

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

theorem Nock.Verb.EvN_op11_dyn {subj tb clue body x} :
    Ev subj (.cell (.atom 11) (.cell (.cell tb clue) body)) x ↔
      (∃ cv, Ev subj clue cv) ∧ Ev subj body x := by sorry
