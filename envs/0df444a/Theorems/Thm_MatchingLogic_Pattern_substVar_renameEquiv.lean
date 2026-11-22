-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_renameEquiv
-- name    : MatchingLogic.Pattern.substVar_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:02.254783+00:00
-- url     : https://prove2.me/theorems/077db240-85d6-45da-bbe2-4681e26ed58a
-- title:
--   Pattern: subst Var rename Equiv
-- statement:
--   Variable-for-variable substitution commutes with a bijective renaming.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L115-L118

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.substVar_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename e = substVar (e x) (e y) (p.rename e) := by sorry
