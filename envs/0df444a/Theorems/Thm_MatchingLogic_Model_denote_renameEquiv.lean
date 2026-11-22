-- Prove2me | Theorems.Thm_MatchingLogic_Model_denote_renameEquiv
-- name    : MatchingLogic.Model.denote_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:30.327815+00:00
-- url     : https://prove2.me/theorems/ab2d9b7b-8ba9-4bbe-85d8-d2be0c7aab4c
-- title:
--   Model: denote rename Equiv
-- statement:
--   Denotation is unchanged by a bijective change of variable names.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L235-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L235-L239

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Model.denote_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (e : Var ≃ Var') (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename e) = M.denote (rho ∘ e) p := by sorry
