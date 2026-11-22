-- Prove2me | Theorems.Thm_MatchingLogic_witnessed_freshWitnessed_of_isMCS_refuted
-- name    : MatchingLogic.witnessed_freshWitnessed_of_isMCS_refuted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:39.318333+00:00
-- url     : https://prove2.me/theorems/cb51bd76-e152-4a78-8b3d-59ddfe66a5da
-- title:
--   Matching Logic: witnessed fresh Witnessed of is MCS refuted
-- statement:
--   Direct negation of the proposed implication at the counterexample
--   signature.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L161-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean#L161-L166

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

theorem MatchingLogic.witnessed_freshWitnessed_of_isMCS_refuted :
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      IsMCS Gamma → Witnessed Gamma → FreshWitnessed Gamma) := by sorry
