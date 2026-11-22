-- Prove2me | Theorems.Thm_MatchingLogic_AppCtx_plug_comp
-- name    : MatchingLogic.AppCtx.plug_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:19.267314+00:00
-- url     : https://prove2.me/theorems/e97f0e32-c46f-4b09-8cc8-ab6943f754a1
-- title:
--   App Ctx: plug comp
-- statement:
--   The App Ctx construction uses the plug comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L50-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean#L50-L56

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
open MatchingLogic.AppCtx

theorem MatchingLogic.AppCtx.plug_comp {Var : Type}
    (outer inner : AppCtx S Var) (p : Pattern S Var) :
    (outer.comp inner).plug p = outer.plug (inner.plug p) := by sorry
