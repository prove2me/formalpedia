-- Prove2me | Theorems.Thm_MatchingLogic_AppCtx_plug_liftSignature
-- name    : MatchingLogic.AppCtx.plug_liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:51.139615+00:00
-- url     : https://prove2.me/theorems/d549abba-d8ac-4129-be47-e03c355ea38a
-- title:
--   App Ctx: plug lift Signature
-- statement:
--   The App Ctx construction uses the plug lift Signature property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L193-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L193-L201

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.AppCtx
omit [DecidableEq Var]

theorem MatchingLogic.AppCtx.plug_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (C : AppCtx (S.restrict F) Var) (p : Pattern (S.restrict F) Var) :
    (C.plug p).liftSignature F = (C.liftSignature F).plug (p.liftSignature F) := by sorry
