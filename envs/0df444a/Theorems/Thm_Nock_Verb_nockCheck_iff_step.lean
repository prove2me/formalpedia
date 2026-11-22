-- Prove2me | Theorems.Thm_Nock_Verb_nockCheck_iff_step
-- name    : Nock.Verb.nockCheck_iff_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:54.717294+00:00
-- url     : https://prove2.me/theorems/ec2ac0d7-206b-4add-984c-b1b5ba88f122
-- title:
--   Verb: nock Check iff step
-- statement:
--   **`Nock` checker ↔ trace consistency (`Step`) + crash.**  `NockCheck a b = true` (paper's
--       accept `0`, main.tex:1118) iff `b` is a `Step`-successor of `a` (`Step a v`, i.e. a
--       consistent transition `Nock(a,v)=0`) or `a` crashes and `b = ⊥` (`b = none`).  This is the
--       genuine biconditional making the two-verb checker 1-1 with the forward semantics `Step`
--       plus the crash branch (defeq to `Verb.nockCheck_eq_true_iff`, since `Step a v := next a =
--       some v`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L430-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L430-L432

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.nockCheck_iff_step {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔ (∃ v, b = some v ∧ Step a v) ∨ (b = none ∧ Crashes a) := by sorry
