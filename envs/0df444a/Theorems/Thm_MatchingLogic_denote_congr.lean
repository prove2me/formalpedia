-- Prove2me | Theorems.Thm_MatchingLogic_denote_congr
-- name    : MatchingLogic.denote_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:50.293086+00:00
-- url     : https://prove2.me/theorems/d3f99bce-4ed8-4c9f-baf4-15ebadf28395
-- title:
--   Matching Logic: denote congr
-- statement:
--   The denotation depends on a valuation only through the free variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L90-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L90-L93

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denote_congr (M : Model S) (φ : Pattern S Var) :
    ∀ (ρ ρ' : Var → M.carrier), (∀ x ∈ FV φ, ρ x = ρ' x) →
      M.denote ρ φ = M.denote ρ' φ := by sorry
