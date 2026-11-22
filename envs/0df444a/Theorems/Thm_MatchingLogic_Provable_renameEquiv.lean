-- Prove2me | Theorems.Thm_MatchingLogic_Provable_renameEquiv
-- name    : MatchingLogic.Provable.renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:34.343883+00:00
-- url     : https://prove2.me/theorems/45a304a0-3486-467a-89fa-0f2d6c404a45
-- title:
--   Provable: rename Equiv
-- statement:
--   Derivability is invariant under a bijective change of variable names.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L317-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L317-L321

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.Provable.renameEquiv [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename e '' Gamma) (phi.rename e) := by sorry
