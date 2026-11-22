-- Prove2me | Theorems.Thm_MatchingLogic_subset_localize
-- name    : MatchingLogic.subset_localize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:42.234508+00:00
-- url     : https://prove2.me/theorems/1985cb70-0520-4ba0-9658-e4ac091484ac
-- title:
--   Matching Logic: subset localize
-- statement:
--   `Γ ⊆ Δ_Γ`, by taking `p = ε`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L42-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L42-L44

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]

theorem MatchingLogic.subset_localize (Γ : Set (Pattern S Var)) : Γ ⊆ localize Γ := by sorry
