-- Prove2me | Theorems.Thm_MatchingLogic_Provable_renameInjective
-- name    : MatchingLogic.Provable.renameInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:30.999805+00:00
-- url     : https://prove2.me/theorems/e2fc2821-49a6-42b2-a5f0-ce6bedce10c7
-- title:
--   Provable: rename Injective
-- statement:
--   Every raw derivation embeds into a larger variable type.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L267-L314
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L267-L314

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Provable.renameInjective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename f '' Gamma) (phi.rename f) := by sorry
