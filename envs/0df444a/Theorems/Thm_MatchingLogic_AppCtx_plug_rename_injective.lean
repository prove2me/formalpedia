-- Prove2me | Theorems.Thm_MatchingLogic_AppCtx_plug_rename_injective
-- name    : MatchingLogic.AppCtx.plug_rename_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:56.49943+00:00
-- url     : https://prove2.me/theorems/a6292cde-1d4e-4acd-aba1-1167f72cb464
-- title:
--   App Ctx: plug rename injective
-- statement:
--   Plugging an application context commutes with a variable renaming.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L177-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Renaming.lean#L177-L189

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}

theorem MatchingLogic.AppCtx.plug_rename_injective
    (f : Var → Var') (C : AppCtx S Var) (p : Pattern S Var) :
    (C.plug p).rename f = (C.rename f).plug (p.rename f) := by sorry
