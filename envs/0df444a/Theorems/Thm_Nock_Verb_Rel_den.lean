-- Prove2me | Theorems.Thm_Nock_Verb_Rel_den
-- name    : Nock.Verb.Rel_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:42.580824+00:00
-- url     : https://prove2.me/theorems/042d57f4-35d1-4388-874e-a2b105d8a181
-- title:
--   Verb: Rel den
-- statement:
--   **STEP-CONG (den-preservation of `Rel`).**  If `Rel v w` and `v` is edit-well-formed,
--       then `v` and `w` have the same denotation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1105-L1161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1105-L1161

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

theorem Nock.Verb.Rel_den : ∀ (n : Nat) (v w : Verb), v.noun.size ≤ n → Rel v w → editOk v = true →
    ∀ x, (Den v x ↔ Den w x) := by sorry
