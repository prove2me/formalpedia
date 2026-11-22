-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_liftSignature_conj
-- name    : MatchingLogic.Pattern.liftSignature_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:15.72883+00:00
-- url     : https://prove2.me/theorems/c91a4211-7386-48b5-a06b-dd27bc4ca3ad
-- title:
--   Pattern: lift Signature conj
-- statement:
--   Lifting distributes through the fixed bracketing of a finite conjunction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L74-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L74-L79

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Theorems.Thm_MatchingLogic_Provable_liftSignature

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern
omit [DecidableEq Var]

theorem MatchingLogic.Pattern.liftSignature_conj [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern (S.restrict F) Var)) :
    (conj l).liftSignature F = conj (l.map (Pattern.liftSignature F)) := by sorry
