-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_symbolSupport_subset_symbolSupportList
-- name    : MatchingLogic.Pattern.symbolSupport_subset_symbolSupportList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:49.920398+00:00
-- url     : https://prove2.me/theorems/0228a1d5-2877-429d-9327-709e657c1080
-- title:
--   Pattern: symbol Support subset symbol Support List
-- statement:
--   Every pattern in a finite list is supported by that list's support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L39-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L39-L49

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
omit [DecidableEq Var]

theorem MatchingLogic.Pattern.symbolSupport_subset_symbolSupportList [DecidableEq S.Sym]
    (l : List (Pattern S Var)) {p : Pattern S Var} (hp : p ∈ l) :
    p.symbolSupport ⊆ Pattern.symbolSupportList l := by sorry
