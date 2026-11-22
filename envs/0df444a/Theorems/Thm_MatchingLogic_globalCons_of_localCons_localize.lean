-- Prove2me | Theorems.Thm_MatchingLogic_globalCons_of_localCons_localize
-- name    : MatchingLogic.globalCons_of_localCons_localize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:48.067949+00:00
-- url     : https://prove2.me/theorems/b5b2576a-b122-41ae-b287-0f43a9df7386
-- title:
--   Matching Logic: global Cons of local Cons localize
-- statement:
--   **Lemma 7.**  If `Δ_Γ ⊨loc φ` then `Γ ⊨ φ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L116-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L116-L126

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.globalCons_of_localCons_localize {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (h : LocalCons (localize Γ) φ) : GlobalCons Γ φ := by sorry
