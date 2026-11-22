-- Prove2me | Theorems.Thm_MatchingLogic_Model_sat_iff_denote_eq_univ
-- name    : MatchingLogic.Model.sat_iff_denote_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:23.25738+00:00
-- url     : https://prove2.me/theorems/a296e6e9-b255-485b-baa0-bfca325f14c8
-- title:
--   Model: sat iff denote eq univ
-- statement:
--   For closed `φ`, `M ⊨ φ` says exactly `⟦φ⟧ = M`, with no valuation
--   quantifier left (paper, Section 2, "Closed patterns").
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L132-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Semantics.lean#L132-L141

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Model.sat_iff_denote_eq_univ (M : Model S) {φ : Pattern S Var}
    (hφ : Closed φ) (ρ : Var → M.carrier) :
    M.Sat φ ↔ M.denote ρ φ = Set.univ := by sorry
