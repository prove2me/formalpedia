-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
-- name    : MatchingLogic.Pattern.AlphaEq.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:53.818814+00:00
-- url     : https://prove2.me/theorems/a639278e-d5f4-44d8-8729-9cba167b22e4
-- title:
--   Alpha Eq: symm
-- statement:
--   The Alpha Eq construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L178-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L178-L179

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
open MatchingLogic.Pattern.AlphaEq

theorem MatchingLogic.Pattern.AlphaEq.symm {p q : Pattern S Nat} (h : AlphaEq p q) : AlphaEq q p := by sorry
