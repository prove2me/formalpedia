-- Prove2me | Theorems.Thm_MatchingLogic_witnessed_freshWitnessed_of_isMCS_counterexample
-- name    : MatchingLogic.witnessed_freshWitnessed_of_isMCS_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:37.774159+00:00
-- url     : https://prove2.me/theorems/933d2bef-b3e0-42b9-8bd6-2e9f990e0376
-- title:
--   Matching Logic: witnessed fresh Witnessed of is MCS counterexample
-- statement:
--   A concrete counterexample to the proposed collapse theorem, including the
--   maximality obligation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L153-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L153-L157

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

theorem MatchingLogic.witnessed_freshWitnessed_of_isMCS_counterexample :
    ∃ Gamma : Set (Pattern WitnessCollapseSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ FreshWitnessed Gamma := by sorry
