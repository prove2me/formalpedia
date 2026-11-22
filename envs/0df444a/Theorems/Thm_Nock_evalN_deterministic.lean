-- Prove2me | Theorems.Thm_Nock_evalN_deterministic
-- name    : Nock.evalN_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:06.011994+00:00
-- url     : https://prove2.me/theorems/728d28da-0058-4f71-96a4-4db4c917863d
-- title:
--   Nock: eval N deterministic
-- statement:
--   **`evalN` is a partial function (output uniqueness).**  Two successful evaluations of the
--       same `subject`/`formula`, at any fuel budgets, return the same noun.  Fuel controls only
--       whether evaluation finishes, never the result.  Proof: bump both to the common fuel
--       `max n m` by `evalN_mono`, then `some` is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L46-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L46-L49

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.evalN_deterministic {n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalN n s form = some r₁) (h₂ : evalN m s form = some r₂) : r₁ = r₂ := by sorry
