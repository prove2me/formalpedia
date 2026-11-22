-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_signatureNatCode_injective
-- name    : MatchingLogic.Pattern.signatureNatCode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:36.654259+00:00
-- url     : https://prove2.me/theorems/7362c420-0035-46fe-a6ac-bb07864ef668
-- title:
--   Pattern: signature Nat Code injective
-- statement:
--   The natural serialization is injective whenever the symbol type is encodable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L232-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L232-L284

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.signatureNatCode_injective {T : Signature} [Encodable T.Sym] :
    Function.Injective (@signatureNatCode T _) := by sorry
