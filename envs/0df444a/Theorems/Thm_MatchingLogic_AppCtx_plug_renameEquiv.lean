-- Prove2me | Theorems.Thm_MatchingLogic_AppCtx_plug_renameEquiv
-- name    : MatchingLogic.AppCtx.plug_renameEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:22.168897+00:00
-- url     : https://prove2.me/theorems/c23166cb-f2d6-4ca1-b599-2f56abd34009
-- title:
--   App Ctx: plug rename Equiv
-- statement:
--   Renaming commutes with plugging an application context.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L192-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L192-L195

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.AppCtx.plug_renameEquiv
    (e : Var ≃ Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename e = (C.rename e).plug (p.rename e) := by sorry
