-- Prove2me | Theorems.Thm_Nock_paper_field_bridge
-- name    : Nock.paper_field_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:19.382339+00:00
-- url     : https://prove2.me/theorems/ed06c2c9-3a8b-4659-a03d-3f726c1dcb70
-- title:
--   Nock: paper field bridge
-- statement:
--   **Paper ↔ finite-field bridge.**  On `q`-bounded inputs (every atom is a canonical residue
--       `< q`), a successful *guarded* paper-fragment run makes all five formalizations of the paper's
--       evaluation agree on one noun, which is again `q`-bounded:
--
--       * the small-step machine `Verb.runProgram` (`main.tex:1052–1083`),
--       * the Nat paper oracle `evalPaper`,
--       * the strict modular paper oracle `evalPaperMod q` (`main.tex:1531–1534`),
--       * the full modular evaluator `FieldEmbedding.evalFBy q`, and
--       * the Nat reference `evalN`.
--
--       The single hypothesis `evalGPaper q fuel s f = some r` is no-overflow: it is discharged by
--       *running* the guarded evaluator, not assumed.  The `BoundedBy q r` conclusion then delivers
--       leaf-cast injectivity for free (`bridge_reflects_field_equality`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L253-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L253-L267

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.paper_field_bridge (q : Nat) (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : evalGPaper q fuel s f = some r) :
    (∃ n, Verb.runProgram n s f = some r) ∧
      evalPaper fuel s f = some r ∧
      evalPaperMod q fuel s f = some r ∧
      FieldEmbedding.evalFBy q fuel s f = some r ∧
      evalN fuel s f = some r ∧
      FieldEmbedding.BoundedBy q r := by sorry
