-- Prove2me | Theorems.Thm_Nock_Verb_evalPaper_atom_none
-- name    : Nock.Verb.evalPaper_atom_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:23.589099+00:00
-- url     : https://prove2.me/theorems/b8a9541e-383b-42d6-98b0-81ee719197df
-- title:
--   Verb: eval Paper atom none
-- statement:
--   `evalPaper` crashes when the formula is an atom (bare noun, no opcode).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1654-L1656
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1654-L1656

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

theorem Nock.Verb.evalPaper_atom_none (f : Nat) (s : Noun) (k : Nat) :
    evalPaper f s (.atom k) = none := by sorry
