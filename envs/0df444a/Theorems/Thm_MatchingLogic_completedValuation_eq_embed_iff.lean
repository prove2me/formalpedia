-- Prove2me | Theorems.Thm_MatchingLogic_completedValuation_eq_embed_iff
-- name    : MatchingLogic.completedValuation_eq_embed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:55.843634+00:00
-- url     : https://prove2.me/theorems/d3aa3a7d-7cad-45b9-9874-69b0364a286b
-- title:
--   Matching Logic: completed Valuation eq embed iff
-- statement:
--   The selection is well-defined: it names an embedded world exactly when
--   that world contains the variable, with uniqueness supplied by Lemma 78.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L254-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Completion.lean#L254-L279

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion

theorem MatchingLogic.completedValuation_eq_embed_iff (root : CanonicalCarrier S) (x : Nat)
    (world : GeneratedCarrier root) :
    completedValuation root x = completedEmbed root world ↔
      Pattern.var x ∈ world.val.val := by sorry
