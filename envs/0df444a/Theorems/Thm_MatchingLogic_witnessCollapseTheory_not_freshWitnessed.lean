-- Prove2me | Theorems.Thm_MatchingLogic_witnessCollapseTheory_not_freshWitnessed
-- name    : MatchingLogic.witnessCollapseTheory_not_freshWitnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:53.548156+00:00
-- url     : https://prove2.me/theorems/6a715f4a-a8ed-4656-80b5-31ed59365b97
-- title:
--   Matching Logic: witness Collapse Theory not fresh Witnessed
-- statement:
--   The existential `∃ 0. var 0` belongs to the pointed theory, but every
--   fresh name denotes `false`, so no fresh Henkin implication belongs to it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L130-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L130-L149

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}

theorem MatchingLogic.witnessCollapseTheory_not_freshWitnessed :
    ¬ FreshWitnessed witnessCollapseTheory := by sorry
