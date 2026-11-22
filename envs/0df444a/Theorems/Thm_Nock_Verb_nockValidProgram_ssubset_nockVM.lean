-- Prove2me | Theorems.Thm_Nock_Verb_nockValidProgram_ssubset_nockVM
-- name    : Nock.Verb.nockValidProgram_ssubset_nockVM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:41.506524+00:00
-- url     : https://prove2.me/theorems/4b07d063-4ed0-4df1-99d1-dbcb3e37e697
-- title:
--   Verb: nock Valid Program ssubset nock VM
-- statement:
--   **Strict inclusion (main.tex:1145).**  `NockValidProgram^Λ ⊊ NockVM^Λ`: every valid program
--       is finite of length `≤ Λ` (`⊆`, via `finite_of_valid`), and the containment is *strict* —
--       e.g. the terminal leaf `0` is a finite verb of length `1 ≤ Λ` that is **not** a Nock program
--       (it is not of the form `*[subject, formula]`; main.tex:1145 "not all elements of `NockVM^Λ`
--       are actually programs").  The side condition `1 ≤ Λ` is *necessary*: for `Λ = 0` both
--       languages are empty (every verb has `≥ 1` leaf), so `∅ ⊊ ∅` fails; the paper's `⊊` is meant
--       for the non-degenerate range.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L363-L371
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L363-L371

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.nockValidProgram_ssubset_nockVM {Λ : Nat} (hΛ : 1 ≤ Λ) :
    SSubLang (NockValidProgramΛ Λ) (FiniteΛ Λ) := by sorry
