-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_spec
-- name    : MatchingLogic.Pattern.captureAvoidingSubst_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:45.961545+00:00
-- url     : https://prove2.me/theorems/3b42b954-c25e-4c91-a7f8-c106e7eeb109
-- title:
--   Pattern: capture Avoiding Subst spec
-- statement:
--   The Pattern construction uses the capture Avoiding Subst spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L362-L365
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L362-L365

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

theorem MatchingLogic.Pattern.captureAvoidingSubst_spec (x y : Nat) (p : Pattern S Nat) :
    IsCaptureAvoidingSubst x y p (captureAvoidingSubst x y p) := by sorry
