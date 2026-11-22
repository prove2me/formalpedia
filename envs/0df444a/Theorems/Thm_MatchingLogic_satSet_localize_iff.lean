-- Prove2me | Theorems.Thm_MatchingLogic_satSet_localize_iff
-- name    : MatchingLogic.satSet_localize_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:44.030939+00:00
-- url     : https://prove2.me/theorems/afc1ca7f-9fbc-4fce-9fb6-e204b15700d7
-- title:
--   Matching Logic: sat Set localize iff
-- statement:
--   `M ⊨ Γ` and `M ⊨ Δ_Γ` are equivalent: localizing does not change the
--   models.  Proved here from Lemma 4 rather than from necessitation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L101-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L101-L113

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.satSet_localize_iff (M : Model S) {Γ : Set (Pattern S Var)}
    : M.SatSet (localize Γ) ↔ M.SatSet Γ := by sorry
