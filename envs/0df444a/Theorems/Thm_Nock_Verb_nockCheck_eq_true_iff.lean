-- Prove2me | Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff
-- name    : Nock.Verb.nockCheck_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:06.365959+00:00
-- url     : https://prove2.me/theorems/e9e81199-4795-48a8-9503-b3ce2ad00239
-- title:
--   Verb: nock Check eq true iff
-- statement:
--   **`NockCheck` ↔ forward semantics + crash.**  The two-verb checker accepts `(a, b)`
--       (returns `true` = the paper's `0`) iff `b` is a genuine one-step successor of `a`
--       (`next a = some v`, i.e. `Step a v`) OR `a` crashes and `b = ⊥` (`b = none`).  This is a
--       genuine biconditional: `NockCheck` is 1-1 with `next` (on non-⊥ successors) together with
--       the crash branch — the checker `Nock(Tᵢ,Tᵢ₊₁)=0` and the forward map coincide exactly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L935-L982
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L935-L982

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.nockCheck_eq_true_iff {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔
      (∃ v, b = some v ∧ next a = some v) ∨ (b = none ∧ Crashes a) := by sorry
