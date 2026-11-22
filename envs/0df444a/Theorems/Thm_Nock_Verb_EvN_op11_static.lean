-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op11_static
-- name    : Nock.Verb.EvN_op11_static
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:33.691727+00:00
-- url     : https://prove2.me/theorems/9af9092a-7a4e-4d4b-bc7a-d45498213257
-- title:
--   Verb: Ev N op11 static
-- statement:
--   **`evalN` OP₁₁ static clause**, as a big-step equivalence: `*[a 11 t d] = *[a d]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L662-L669
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L662-L669

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

theorem Nock.Verb.EvN_op11_static {subj t body x} :
    Ev subj (.cell (.atom 11) (.cell (.atom t) body)) x ↔ Ev subj body x := by sorry
