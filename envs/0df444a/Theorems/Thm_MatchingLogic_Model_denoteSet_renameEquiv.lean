-- Prove2me | Theorems.Thm_MatchingLogic_Model_denoteSet_renameEquiv
-- name    : MatchingLogic.Model.denoteSet_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:32.865505+00:00
-- url     : https://prove2.me/theorems/4c299d44-bb35-4a5e-96bf-eeefd55e1fb8
-- title:
--   Model: denote Set rename Equiv
-- statement:
--   Conjunctive denotation of a theory is unchanged by a bijective renaming.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L260-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L260-L264

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Model.denoteSet_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename e '' Delta) = M.denoteSet (rho ∘ e) Delta := by sorry
