-- Prove2me | Theorems.Thm_MatchingLogic_restrictedPatternNatCountable
-- name    : MatchingLogic.restrictedPatternNatCountable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:44.515428+00:00
-- url     : https://prove2.me/theorems/8b38bff8-af60-40b2-8069-890902c71603
-- title:
--   Matching Logic: restricted Pattern Nat Countable
-- statement:
--   A finite signature yields a countable type of natural-variable patterns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L289-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L289-L298

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.restrictedPatternNatCountable
    (F : Finset S.Sym) : Countable (Pattern (S.restrict F) Nat) := by sorry
