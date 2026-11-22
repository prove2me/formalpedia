-- Prove2me | Theorems.Thm_Nock_Verb_denP_iff_evalPaper
-- name    : Nock.Verb.denP_iff_evalPaper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:33.785688+00:00
-- url     : https://prove2.me/theorems/c0268f2d-7536-4a37-917f-8bc6d1022e2b
-- title:
--   Verb: den P iff eval Paper
-- statement:
--   **`denP` ≡ `evalPaper` on program verbs, as partial functions** (cf. `den_iff_evalN`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L122-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L122-L138

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

theorem Nock.Verb.denP_iff_evalPaper (s f r : Noun) :
    (∃ fuel, denP fuel (program s f) = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) := by sorry
