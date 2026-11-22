-- Prove2me | Theorems.Thm_MatchingLogic_Model_denoteSet_renameInjective
-- name    : MatchingLogic.Model.denoteSet_renameInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:30.709479+00:00
-- url     : https://prove2.me/theorems/49f8b314-acf8-43f2-9a60-245c417336db
-- title:
--   Model: denote Set rename Injective
-- statement:
--   Conjunctive denotation commutes with an injective variable embedding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L242-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L242-L257

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Model.denoteSet_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier)
    (Delta : Set (Pattern S Var)) :
    M.denoteSet rho (Pattern.rename f '' Delta) =
      M.denoteSet (rho ∘ f) Delta := by sorry
