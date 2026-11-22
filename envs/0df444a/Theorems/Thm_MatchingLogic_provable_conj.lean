-- Prove2me | Theorems.Thm_MatchingLogic_provable_conj
-- name    : MatchingLogic.provable_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:53.677795+00:00
-- url     : https://prove2.me/theorems/4f01c5ac-53c2-4192-947d-23da683d9f94
-- title:
--   Matching Logic: provable conj
-- statement:
--   Introduce the pinned finite conjunction of a list of derivable patterns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L307-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L307-L313

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.provable_conj {Γ : Set (Pattern S Var)} (l : List (Pattern S Var))
    (h : ∀ δ ∈ l, Provable Γ δ) : Provable Γ (conj l) := by sorry
