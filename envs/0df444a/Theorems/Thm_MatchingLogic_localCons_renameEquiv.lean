-- Prove2me | Theorems.Thm_MatchingLogic_localCons_renameEquiv
-- name    : MatchingLogic.localCons_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:40.4152+00:00
-- url     : https://prove2.me/theorems/3ec1ff54-42bb-4c25-9328-3d1c1e3e8f73
-- title:
--   Matching Logic: local Cons rename Equiv
-- statement:
--   Local consequence is invariant under a bijective change of variable names.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L345-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L345-L348

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.localCons_renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔ LocalCons (Pattern.rename e '' Delta) (phi.rename e) := by sorry
