-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_FV_liftSignature
-- name    : MatchingLogic.Pattern.FV_liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:22.880005+00:00
-- url     : https://prove2.me/theorems/1b407fc3-1d91-4017-b0f6-20210cffa5ab
-- title:
--   Pattern: FV lift Signature
-- statement:
--   Free variables are unchanged by signature lifting.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L111-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L111-L123

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
omit [DecidableEq Var]

theorem MatchingLogic.Pattern.FV_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : Pattern (S.restrict F) Var) :
    FV (p.liftSignature F) = FV p := by sorry
