-- Prove2me | Theorems.Thm_Nock_Verb_runTrace_unique
-- name    : Nock.Verb.runTrace_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:45.560803+00:00
-- url     : https://prove2.me/theorems/1a96faa1-3eef-4cc1-a044-9043e9348c66
-- title:
--   Verb: run Trace unique
-- statement:
--   **The emitted trace is unique.**  Because `next` is a function, any two successful runs of
--       `runTrace` on the same verb — at any fuel budgets — produce the same trace.  This is the
--       executable form of `Thm:deterministic_Trace` (`main.tex:1156–1158`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L181-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L181-L203

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTrace_unique :
    ∀ (fuel₁ fuel₂ : Nat) (v : Verb) (T₁ T₂ : List Verb),
      runTrace fuel₁ v = some T₁ → runTrace fuel₂ v = some T₂ → T₁ = T₂ := by sorry
