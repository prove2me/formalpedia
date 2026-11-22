-- Prove2me | Theorems.Thm_MatchingLogic_Necessity_locality_needs_backwardClosed_nat
-- name    : MatchingLogic.Necessity.locality_needs_backwardClosed_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:55.913943+00:00
-- url     : https://prove2.me/theorems/8a43d848-05a4-45e3-88cd-cf11ac3a018e
-- title:
--   Necessity: locality needs backward Closed nat
-- statement:
--   The paper's setting: countably infinite element variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L110-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L110-L113

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity

theorem MatchingLogic.Necessity.locality_needs_backwardClosed_nat :
    ¬ (∀ (ψ : Pattern S Nat) (ρ ρ' : Nat → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) := by sorry
