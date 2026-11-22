-- Prove2me | Theorems.Thm_MatchingLogic_denoteSet_localize
-- name    : MatchingLogic.denoteSet_localize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:47.835828+00:00
-- url     : https://prove2.me/theorems/04a01c8c-c034-4097-8682-0f953230606b
-- title:
--   Matching Logic: denote Set localize
-- statement:
--   **Lemma 8.**  `⟦Δ_Γ⟧ = {u | ⇝*[u] ⊆ ⟦Γ⟧}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L55-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L55-L71

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denoteSet_localize (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) :
    M.denoteSet ρ (localize Γ) =
      {u | ∀ v, Relation.ReflTransGen M.Step u v → v ∈ M.denoteSet ρ Γ} := by sorry
