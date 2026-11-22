-- Prove2me | Theorems.Thm_MatchingLogic_Model_app_const
-- name    : MatchingLogic.Model.app_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:20.150889+00:00
-- url     : https://prove2.me/theorems/9548e266-2406-468d-b9f6-bf94f4121523
-- title:
--   Model: app const
-- statement:
--   Control 2: a constant is interpreted by a subset of the carrier, and its
--   denotation does not depend on the valuation.  `Fin 0` being empty is what makes
--   the tuple unique.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sanity.lean#L48-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sanity.lean#L48-L59

module
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Model
variable {S : Signature}

theorem MatchingLogic.Model.app_const (M : Model S) (σ : S.Sym) (h : S.arity σ = 0)
    (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A = M.interp σ (fun i => absurd i.isLt (by omega)) := by sorry
