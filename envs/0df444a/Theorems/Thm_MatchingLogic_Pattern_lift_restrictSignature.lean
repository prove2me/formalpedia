-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_lift_restrictSignature
-- name    : MatchingLogic.Pattern.lift_restrictSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:30.1201+00:00
-- url     : https://prove2.me/theorems/db13d309-cb10-4ded-84ed-61d9078ff8bb
-- title:
--   Pattern: lift restrict Signature
-- statement:
--   Lifting a restricted pattern recovers the original ambient pattern.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L69-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L69-L88

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

theorem MatchingLogic.Pattern.lift_restrictSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : Pattern S Var) (h : p.symbolSupport ⊆ F) :
    (p.restrictSignature F h).liftSignature F = p := by sorry
