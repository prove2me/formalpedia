-- Prove2me | Theorems.Thm_MatchingLogic_Necessity_locality_needs_backwardClosed
-- name    : MatchingLogic.Necessity.locality_needs_backwardClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:12.557802+00:00
-- url     : https://prove2.me/theorems/7c5b35cd-8d57-4fb9-8e71-90d3f46669df
-- title:
--   Necessity: locality needs backward Closed
-- statement:
--   **The hypothesis of Lemma 9 cannot be dropped**, for any variable type that
--   has at least one variable.  Without backward closure the conclusion fails, on a
--   three-element model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L97-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L97-L105

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Necessity.locality_needs_backwardClosed (x : Var) :
    ¬ (∀ (ψ : Pattern S Var) (ρ ρ' : Var → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) := by sorry
