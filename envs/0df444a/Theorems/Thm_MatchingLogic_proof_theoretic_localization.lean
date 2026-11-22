-- Prove2me | Theorems.Thm_MatchingLogic_proof_theoretic_localization
-- name    : MatchingLogic.proof_theoretic_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:58.040814+00:00
-- url     : https://prove2.me/theorems/31333037-3f22-495e-9a8f-098baba69749
-- title:
--   Matching Logic: proof theoretic localization
-- statement:
--   **Theorem 14 (proof-theoretic localization).**  `Γ ⊢ φ ↔ Δ_Γ ⊨loc φ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Completeness.lean#L38-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Completeness.lean#L38-L53

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

theorem MatchingLogic.proof_theoretic_localization
    (hL : StrongLocalCompleteness S Var) (hS : Soundness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    Provable Γ φ ↔ LocalCons (localize Γ) φ := by sorry
