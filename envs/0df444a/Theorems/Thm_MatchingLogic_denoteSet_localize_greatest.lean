-- Prove2me | Theorems.Thm_MatchingLogic_denoteSet_localize_greatest
-- name    : MatchingLogic.denoteSet_localize_greatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:37.432888+00:00
-- url     : https://prove2.me/theorems/a32cf8e4-523d-40c1-a808-43814d50dd8b
-- title:
--   Matching Logic: denote Set localize greatest
-- statement:
--   **Lemma 8**, third half: it is the *largest* such set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L88-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L88-L97

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denoteSet_localize_greatest (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) {U : Set M.carrier}
    (hU : M.BackwardClosed U) (hUΓ : U ⊆ M.denoteSet ρ Γ) :
    U ⊆ M.denoteSet ρ (localize Γ) := by sorry
