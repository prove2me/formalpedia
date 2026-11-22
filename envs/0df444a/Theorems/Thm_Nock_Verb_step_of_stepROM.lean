-- Prove2me | Theorems.Thm_Nock_Verb_step_of_stepROM
-- name    : Nock.Verb.step_of_stepROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:50.941103+00:00
-- url     : https://prove2.me/theorems/0b220c60-7c58-4319-8778-d6f886e3521a
-- title:
--   Verb: step of step ROM
-- statement:
--   Every ROM step is a Nock step (`nextROM ⊆ next`; main.tex:1160).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L380-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L380-L380

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.step_of_stepROM {a b : Verb} (h : StepROM a b) : Step a b := by sorry
