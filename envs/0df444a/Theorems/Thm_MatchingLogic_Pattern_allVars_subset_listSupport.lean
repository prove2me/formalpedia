-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_allVars_subset_listSupport
-- name    : MatchingLogic.Pattern.allVars_subset_listSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:13.102487+00:00
-- url     : https://prove2.me/theorems/6868c2e7-71ae-4a27-a2a6-972263100a27
-- title:
--   Pattern: all Vars subset list Support
-- statement:
--   Every member's raw-variable support lies in the list support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L231-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L231-L240

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

theorem MatchingLogic.Pattern.allVars_subset_listSupport {l : List (Pattern S Nat)}
    {p : Pattern S Nat} (hp : p ∈ l) : p.allVars ⊆ (listSupport l).allVars := by sorry
