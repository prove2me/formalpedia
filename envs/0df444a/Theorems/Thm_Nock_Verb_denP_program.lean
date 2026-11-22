-- Prove2me | Theorems.Thm_Nock_Verb_denP_program
-- name    : Nock.Verb.denP_program
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:34.531834+00:00
-- url     : https://prove2.me/theorems/a7380baf-b43a-472d-b155-fd8ece5aad3d
-- title:
--   Verb: den P program
-- statement:
--   `denP` of the initial program verb `*[s, f]` is `evalPaper s f` (cf. `den_program`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L117-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L117-L119

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

theorem Nock.Verb.denP_program (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    denP (fuel + 1) (program s f) = evalPaper fuel s f := by sorry
