-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_complexity_eq
-- name    : MatchingLogic.Pattern.IsCaptureAvoidingSubst.complexity_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:44.312376+00:00
-- url     : https://prove2.me/theorems/011dc3c0-e472-4ecb-8be9-b71f580890fe
-- title:
--   Is Capture Avoiding Subst: complexity eq
-- statement:
--   The Is Capture Avoiding Subst construction uses the complexity eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L382-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L382-L386

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators

theorem MatchingLogic.Pattern.IsCaptureAvoidingSubst.complexity_eq {x y : Nat} {p q : Pattern S Nat}
    (h : IsCaptureAvoidingSubst x y p q) : q.complexity = p.complexity := by sorry
