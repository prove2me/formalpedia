-- Prove2me | Theorems.Thm_MatchingLogic_locality
-- name    : MatchingLogic.locality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:52.717839+00:00
-- url     : https://prove2.me/theorems/1b65e798-0f93-4e3d-81ba-a97a1a05168f
-- title:
--   Matching Logic: locality
-- statement:
--   **Lemma 9 (locality).**  A backward-closed `C` together with one bit per
--   variable -- whether that variable's value lies in `C` -- determines truth on `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L73-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L73-L137

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.locality (M : Model S) {C : Set M.carrier} (hC : M.BackwardClosed C)
    (ψ : Pattern S Var) (ρ ρ' : Var → M.carrier) (h : AgreeOn C ρ ρ') :
    M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C := by sorry
