-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_AlphaEq_alphaEx
-- name    : MatchingLogic.Pattern.AlphaEq.alphaEx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:07.459053+00:00
-- url     : https://prove2.me/theorems/a61bc9dc-464a-4c43-840f-1e462f699ab1
-- title:
--   Alpha Eq: alpha Ex
-- statement:
--   The Alpha Eq construction uses the alpha Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L208-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L208-L212

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

theorem MatchingLogic.Pattern.AlphaEq.alphaEx {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    AlphaEq (.ex x p) (.ex y (substVar x y p)) := by sorry
