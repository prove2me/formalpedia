-- Prove2me | Theorems.Thm_MatchingLogic_AgreeOn_update
-- name    : MatchingLogic.AgreeOn.update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:58.314381+00:00
-- url     : https://prove2.me/theorems/45737be6-108d-4b2f-b50d-3054f93b522d
-- title:
--   Agree On: update
-- statement:
--   `AgreeOn` is preserved by matched updates: updating both valuations at the
--   same variable to the same value keeps them agreeing, whether or not that value
--   lies in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L58-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Locality.lean#L58-L69

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Locality
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.AgreeOn.update {M : Model S} {C : Set M.carrier} {ρ ρ' : Var → M.carrier}
    (h : AgreeOn C ρ ρ') (x : Var) (a : M.carrier) :
    AgreeOn C (Function.update ρ x a) (Function.update ρ' x a) := by sorry
