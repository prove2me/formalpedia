-- Prove2me | Theorems.Thm_MatchingLogic_localCons_renameInjective
-- name    : MatchingLogic.localCons_renameInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:34.753925+00:00
-- url     : https://prove2.me/theorems/d5155ef5-9cec-4b32-b631-b970a289e99e
-- title:
--   Matching Logic: local Cons rename Injective
-- statement:
--   Local consequence is invariant under an injective change to a larger name space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L324-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L324-L342

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.localCons_renameInjective [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      LocalCons (Pattern.rename f '' Delta) (phi.rename f) := by sorry
