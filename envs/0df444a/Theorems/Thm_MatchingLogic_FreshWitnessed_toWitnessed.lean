-- Prove2me | Theorems.Thm_MatchingLogic_FreshWitnessed_toWitnessed
-- name    : MatchingLogic.FreshWitnessed.toWitnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:28.767585+00:00
-- url     : https://prove2.me/theorems/c33b13ef-b984-4d61-a908-0ff96fb5da97
-- title:
--   Fresh Witnessed: to Witnessed
-- statement:
--   The Fresh Witnessed construction uses the to Witnessed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L55-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L55-L59

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed

theorem MatchingLogic.FreshWitnessed.toWitnessed {Gamma : Set (Pattern S Nat)}
    (h : FreshWitnessed Gamma) : Witnessed Gamma := by sorry
