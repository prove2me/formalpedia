-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_renameInjective
-- name    : MatchingLogic.Model.denote_renameInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:42.597286+00:00
-- url     : https://prove2.me/theorems/6aaae171-32bc-49c0-a0b9-85798b13ba18
-- title:
--   Model: denote rename Injective
-- statement:
--   Denotation commutes with an injective variable embedding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L205-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L205-L232

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Model.denote_renameInjective [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename f) = M.denote (rho ∘ f) p := by sorry
