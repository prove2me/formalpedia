-- Prove2me | Theorems.Thm_MatchingLogic_definedness_conservative
-- name    : MatchingLogic.definedness_conservative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:25.724847+00:00
-- url     : https://prove2.me/theorems/6dd8f7ae-abaf-4c86-b5f6-ccb25b4d67e6
-- title:
--   Matching Logic: definedness conservative
-- statement:
--   **Corollary 16 (conservativity of definedness).**
--
--   Note (S) is supplied rather than assumed — `soundness` is a theorem here, and it
--   holds at `defSig S` as at any signature.  (L) remains a hypothesis, inherited
--   from Corollary 15, and is needed at the BASE signature only.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L175-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L175-L198

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.definedness_conservative
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) (x : Var)
    (h : Provable (emb '' Γ ∪ {definednessAxiom (S := S) x}) (emb φ)) :
    Provable Γ φ := by sorry
