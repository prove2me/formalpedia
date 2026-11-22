-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_substVar_of_captureFree
-- name    : MatchingLogic.Model.denote_substVar_of_captureFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:36.666778+00:00
-- url     : https://prove2.me/theorems/99878123-75e7-4d8b-8d78-033f4c7a142d
-- title:
--   Model: denote subst Var of capture Free
-- statement:
--   Semantic substitution for the capture-free variable-for-variable
--   substitution used by rule (3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L67-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Soundness.lean#L67-L121

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
attribute [local instance] Classical.propDecidable

theorem MatchingLogic.Model.denote_substVar_of_captureFree (M : Model S) (ρ : Var → M.carrier)
    {x y : Var} {φ : Pattern S Var} (hcf : CaptureFree x y φ) :
    M.denote ρ (substVar x y φ) =
      M.denote (Function.update ρ x (ρ y)) φ := by sorry
