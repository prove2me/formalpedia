-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_noOverflow_agreeBy
-- name    : Nock.FieldEmbedding.noOverflow_agreeBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:59.126577+00:00
-- url     : https://prove2.me/theorems/8100e23b-1db0-4f50-b8dc-f9ee9ed82e11
-- title:
--   Field Embedding: no Overflow agree By
-- statement:
--   **No-overflow agreement.**  For `q`-bounded inputs, a successful guarded run contains no
--       modular wrap at `q`, so the Nat and modulo-`q` evaluators return the same `q`-bounded noun.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L566-L569
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L566-L569

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.noOverflow_agreeBy {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (hno : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r := by sorry
