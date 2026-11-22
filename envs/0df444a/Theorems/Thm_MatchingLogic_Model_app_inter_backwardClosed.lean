-- Prove2me | Theorems.Thm_MatchingLogic_Model_app_inter_backwardClosed
-- name    : MatchingLogic.Model.app_inter_backwardClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:43.486544+00:00
-- url     : https://prove2.me/theorems/0002a10a-6e4d-4a91-a836-1cdf9274cd6f
-- title:
--   Model: app inter backward Closed
-- statement:
--   The concrete identity behind the `app`/symbol case of the paper's proof:
--   `σ_M(A₁,…,Aₙ) ∩ C = σ_M(A₁∩C,…,Aₙ∩C) ∩ C`.  Backward closure of `C` is used to
--   pull each witnessing tuple entry into `C` once the produced point already lies
--   in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L44-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L44-L53

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Model.app_inter_backwardClosed {M : Model S} {C : Set M.carrier}
    (hC : M.BackwardClosed C) (σ : S.Sym) (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A ∩ C = M.app σ (fun i => A i ∩ C) ∩ C := by sorry
