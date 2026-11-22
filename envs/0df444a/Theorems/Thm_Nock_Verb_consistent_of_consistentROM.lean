-- Prove2me | Theorems.Thm_Nock_Verb_consistent_of_consistentROM
-- name    : Nock.Verb.consistent_of_consistentROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:50.956467+00:00
-- url     : https://prove2.me/theorems/ee9c351c-0156-47dc-a4b8-2831645c6973
-- title:
--   Verb: consistent of consistent ROM
-- statement:
--   Every consistent ROM trace is a consistent Nock trace (ROM steps are Nock steps).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L391-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L391-L394

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.consistent_of_consistentROM : ∀ (T : List Verb), ConsistentR StepROM T → Consistent T
  := by sorry
