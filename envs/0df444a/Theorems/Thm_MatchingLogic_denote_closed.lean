-- Prove2me | Theorems.Thm_MatchingLogic_denote_closed
-- name    : MatchingLogic.denote_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:56.440868+00:00
-- url     : https://prove2.me/theorems/3836711b-be0a-4caf-829f-1dba976a0de6
-- title:
--   Matching Logic: denote closed
-- statement:
--   For a closed pattern the denotation does not depend on the valuation at all;
--   this is what licenses the paper's `⟦ψ⟧` notation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L97-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L97-L103

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denote_closed (M : Model S) {φ : Pattern S Var} (hφ : Closed φ)
    (ρ ρ' : Var → M.carrier) : M.denote ρ φ = M.denote ρ' φ := by sorry
