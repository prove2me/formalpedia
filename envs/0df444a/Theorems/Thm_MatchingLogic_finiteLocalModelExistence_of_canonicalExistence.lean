-- Prove2me | Theorems.Thm_MatchingLogic_finiteLocalModelExistence_of_canonicalExistence
-- name    : MatchingLogic.finiteLocalModelExistence_of_canonicalExistence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:30.217832+00:00
-- url     : https://prove2.me/theorems/2556e957-b0b0-4f7e-8df5-f0b7805d69cd
-- title:
--   Matching Logic: finite Local Model Existence of canonical Existence
-- statement:
--   Conditional finite pointed-model existence, obtained from a fresh-witnessed
--   MCS root and the completed canonical Truth Lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/ModelExistence.lean#L42-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/ModelExistence.lean#L42-L55

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatModelExistence

theorem MatchingLogic.finiteLocalModelExistence_of_canonicalExistence
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    FiniteLocalModelExistence S Nat := by sorry
