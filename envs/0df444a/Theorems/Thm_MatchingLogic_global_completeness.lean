-- Prove2me | Theorems.Thm_MatchingLogic_global_completeness
-- name    : MatchingLogic.global_completeness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:02.456879+00:00
-- url     : https://prove2.me/theorems/25b71a5b-63bc-4b5b-84eb-efc800a5ef02
-- title:
--   Matching Logic: global completeness
-- statement:
--   **Corollary 15 (one-sorted global completeness).**  `Γ ⊨ φ ↔ Γ ⊢ φ`.
--
--   This is the paper's main positive result, and entry point (ii) of its
--   mechanization challenge: Corollary 15 with (L) and (S) assumed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Completeness.lean#L59-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Completeness.lean#L59-L65

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Completeness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.global_completeness
    (hL : StrongLocalCompleteness S Var) (hS : Soundness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ Provable Γ φ := by sorry
