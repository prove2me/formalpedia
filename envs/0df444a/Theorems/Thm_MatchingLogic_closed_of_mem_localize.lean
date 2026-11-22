-- Prove2me | Theorems.Thm_MatchingLogic_closed_of_mem_localize
-- name    : MatchingLogic.closed_of_mem_localize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:36.285255+00:00
-- url     : https://prove2.me/theorems/41e01105-6d9c-406d-b4af-c3c75b4587d6
-- title:
--   Matching Logic: closed of mem localize
-- statement:
--   Every member of `Δ_Γ` is closed when every member of `Γ` is, so `⟦Δ_Γ⟧` is
--   well defined.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L49-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Localization.lean#L49-L52

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

theorem MatchingLogic.closed_of_mem_localize {Γ : Set (Pattern S Var)}
    (hΓ : ∀ γ ∈ Γ, Closed γ) : ∀ ψ ∈ localize Γ, Closed ψ := by sorry
