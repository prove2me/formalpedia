-- Prove2me | Theorems.Thm_MatchingLogic_backwardClosed_denoteSet_localize
-- name    : MatchingLogic.backwardClosed_denoteSet_localize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:42.879834+00:00
-- url     : https://prove2.me/theorems/c8354d20-1532-4f33-8d8a-d8aead6e6508
-- title:
--   Matching Logic: backward Closed denote Set localize
-- statement:
--   **Lemma 8**, second half: `⟦Δ_Γ⟧` is backward closed and contained in
--   `⟦Γ⟧`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L75-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L75-L85

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.backwardClosed_denoteSet_localize (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) :
    M.BackwardClosed (M.denoteSet ρ (localize Γ)) ∧
      M.denoteSet ρ (localize Γ) ⊆ M.denoteSet ρ Γ := by sorry
