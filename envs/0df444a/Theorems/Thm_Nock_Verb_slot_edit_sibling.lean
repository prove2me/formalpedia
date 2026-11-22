-- Prove2me | Theorems.Thm_Nock_Verb_slot_edit_sibling
-- name    : Nock.Verb.slot_edit_sibling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:21:44.725187+00:00
-- url     : https://prove2.me/theorems/0e3b0bec-efc0-4124-976b-dd7f8a58c6f1
-- title:
--   Verb: slot edit sibling
-- statement:
--   **Sibling carry.**  If editing `old` at axis `ax` succeeds, every off-path sibling subtree
--       encountered from `ax` to the root is unchanged in the result.  Thus an edit cannot mutate
--       either the target's immediate sibling or a sibling branching from any proper ancestor of the
--       target.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1565-L1580
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1565-L1580

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

theorem Nock.Verb.slot_edit_sibling {ax sib : Nat} (hsib : SiblingOf ax sib) :
    ∀ {new old res : Noun},
      Noun.edit ax new old = some res → Noun.slot sib res = Noun.slot sib old := by sorry
