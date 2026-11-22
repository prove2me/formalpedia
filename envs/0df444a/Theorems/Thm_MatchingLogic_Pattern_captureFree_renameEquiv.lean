-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureFree_renameEquiv
-- name    : MatchingLogic.Pattern.captureFree_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:00.494265+00:00
-- url     : https://prove2.me/theorems/ef3319b5-e026-4ac3-b6e1-a32481561d8d
-- title:
--   Pattern: capture Free rename Equiv
-- statement:
--   A bijective renaming preserves the capture-freedom side condition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L143-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L143-L147

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

theorem MatchingLogic.Pattern.captureFree_renameEquiv
    (e : Var ≃ Var') {x y : Var} {p : Pattern S Var}
    (h : CaptureFree x y p) :
    CaptureFree (e x) (e y) (p.rename e) := by sorry
