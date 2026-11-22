-- Prove2me | Theorems.Thm_Nock_Verb_den_program
-- name    : Nock.Verb.den_program
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:12.777553+00:00
-- url     : https://prove2.me/theorems/67647673-0776-4411-8a79-2395b6c696ef
-- title:
--   Verb: den program
-- statement:
--   `den` of the initial program verb `*[s, f]` equals `evalN s f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L122-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L122-L124

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_program (s f : Noun) (fuel : Nat) (hs : s.size ≤ fuel) (hf : f.size ≤ fuel) :
    den (fuel + 1) (program s f) = evalN fuel s f := by sorry
