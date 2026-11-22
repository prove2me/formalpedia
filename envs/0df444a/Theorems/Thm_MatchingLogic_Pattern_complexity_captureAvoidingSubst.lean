-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_complexity_captureAvoidingSubst
-- name    : MatchingLogic.Pattern.complexity_captureAvoidingSubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:37.343666+00:00
-- url     : https://prove2.me/theorems/c9e28a1b-4c81-4574-97e1-da65a48745d9
-- title:
--   Pattern: complexity capture Avoiding Subst
-- statement:
--   Total substitution preserves structural complexity, so the substituted body
--   is available to the strong induction used by the Truth Lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L377-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L377-L380

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

theorem MatchingLogic.Pattern.complexity_captureAvoidingSubst (x y : Nat) (p : Pattern S Nat) :
    (captureAvoidingSubst x y p).complexity = p.complexity := by sorry
