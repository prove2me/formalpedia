-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_liftSignature_restrictList
-- name    : MatchingLogic.Pattern.liftSignature_restrictList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:11.511538+00:00
-- url     : https://prove2.me/theorems/eb0395bf-8aaf-46cd-93d8-82cc9f42b661
-- title:
--   Pattern: lift Signature restrict List
-- statement:
--   Lifting a restricted finite list recovers the original list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L62-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L62-L70

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

theorem MatchingLogic.Pattern.liftSignature_restrictList [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern S Var)) (h : ∀ p ∈ l, p.symbolSupport ⊆ F) :
    (restrictList F l h).map (Pattern.liftSignature F) = l := by sorry
