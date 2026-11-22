-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq
-- name    : MatchingLogic.Pattern.avoidBinder_alphaEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:04.287802+00:00
-- url     : https://prove2.me/theorems/15c14dfe-8242-4178-a99a-366dfffa7f3f
-- title:
--   Pattern: avoid Binder alpha Eq
-- statement:
--   The Pattern construction uses the avoid Binder alpha Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L314-L332
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L314-L332

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

theorem MatchingLogic.Pattern.avoidBinder_alphaEq (y : Nat) (p : Pattern S Nat) :
    AlphaEq p (avoidBinder y p) := by sorry
