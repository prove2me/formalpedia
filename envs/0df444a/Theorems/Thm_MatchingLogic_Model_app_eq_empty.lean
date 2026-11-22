-- Prove2me | Theorems.Thm_MatchingLogic_Model_app_eq_empty
-- name    : MatchingLogic.Model.app_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:57.382805+00:00
-- url     : https://prove2.me/theorems/7bc55871-bfa1-4af9-8a4f-ae54e74c5f51
-- title:
--   Model: app eq empty
-- statement:
--   Control 1: the pointwise extension is `∅` as soon as one argument is
--   (paper, Section 2, sentence after the display).  This would fail if `app` used
--   `∀ i, a i ∈ A i` with an existential over a *partial* tuple, or if it forgot the
--   tuple entirely.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sanity.lean#L35-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sanity.lean#L35-L43

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

theorem MatchingLogic.Model.app_eq_empty (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ)) (h : A i = ∅) :
    M.app σ A = ∅ := by sorry
