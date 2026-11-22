-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_rename_injective
-- name    : MatchingLogic.Pattern.substVar_rename_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:57.924968+00:00
-- url     : https://prove2.me/theorems/e80c4cd5-5c95-49eb-9475-8b3c373cf092
-- title:
--   Pattern: subst Var rename injective
-- statement:
--   Variable substitution commutes with an injective renaming.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L94-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L94-L112

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

theorem MatchingLogic.Pattern.substVar_rename_injective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f) (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename f = substVar (f x) (f y) (p.rename f) := by sorry
