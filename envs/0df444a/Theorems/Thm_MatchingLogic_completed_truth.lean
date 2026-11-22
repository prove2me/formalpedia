-- Prove2me | Theorems.Thm_MatchingLogic_completed_truth
-- name    : MatchingLogic.completed_truth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:42.736261+00:00
-- url     : https://prove2.me/theorems/2a2c0f6d-88e1-4504-8d79-cc007ed202ca
-- title:
--   Matching Logic: completed truth
-- statement:
--   Source Lemma 81, conditional only on the separately isolated canonical
--   Existence Lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Truth.lean#L173-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Truth.lean#L173-L179

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
open scoped BigOperators
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatTruth

theorem MatchingLogic.completed_truth (hExist : CanonicalExistenceProperty S)
    (root : CanonicalCarrier S) (world : GeneratedCarrier root)
    (p : Pattern S Nat) :
    p ∈ world.val.val ↔
      completedEmbed root world ∈
        (completedModel root).denote (completedValuation root) p := by sorry
