-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
-- name    : MatchingLogic.Pattern.AlphaEq.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:06.722259+00:00
-- url     : https://prove2.me/theorems/1e066218-f725-4d60-9952-0ad9cdd3b88f
-- title:
--   Alpha Eq: trans
-- statement:
--   The Alpha Eq construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L181-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L181-L185

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

theorem MatchingLogic.Pattern.AlphaEq.trans {p q r : Pattern S Nat} (hpq : AlphaEq p q) (hqr : AlphaEq q r) :
    AlphaEq p r := by sorry
