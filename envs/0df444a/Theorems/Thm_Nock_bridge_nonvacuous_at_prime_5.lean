-- Prove2me | Theorems.Thm_Nock_bridge_nonvacuous_at_prime_5
-- name    : Nock.bridge_nonvacuous_at_prime_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:16.107854+00:00
-- url     : https://prove2.me/theorems/1e273c00-3907-4554-b3d1-e67253f959db
-- title:
--   Nock: bridge nonvacuous at prime 5
-- statement:
--   **Non-vacuity at a genuine prime.**  `*[0 [4 [1 3]]] = 4` at `q = 5`, where `ZMod q` really is a
--       field, with the full six-fold bridge conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L310-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L310-L320

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.bridge_nonvacuous_at_prime_5 :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      FieldEmbedding.evalFBy 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.atom 4) := by sorry
