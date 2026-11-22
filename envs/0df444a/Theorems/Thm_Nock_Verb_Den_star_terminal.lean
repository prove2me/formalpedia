-- Prove2me | Theorems.Thm_Nock_Verb_Den_star_terminal
-- name    : Nock.Verb.Den_star_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:32.63529+00:00
-- url     : https://prove2.me/theorems/e20034a6-ee40-4748-bd37-22f064661a8e
-- title:
--   Verb: Den star terminal
-- statement:
--   Big-step denotation of a `*`-node with *both* children terminal is `evalN` of the two
--       underlying nouns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L632-L641
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L632-L641

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

theorem Nock.Verb.Den_star_terminal {n1 t x} (h1 : isTerminal n1 = true) (ht : isTerminal t = true) :
    Den (.node .star n1 t) x ↔ Ev n1.noun t.noun x := by sorry
