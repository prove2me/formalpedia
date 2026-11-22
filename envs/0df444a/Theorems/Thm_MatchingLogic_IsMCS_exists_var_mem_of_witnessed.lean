-- Prove2me | Theorems.Thm_MatchingLogic_IsMCS_exists_var_mem_of_witnessed
-- name    : MatchingLogic.IsMCS.exists_var_mem_of_witnessed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:13.527061+00:00
-- url     : https://prove2.me/theorems/b3a3e578-d328-4706-8ab0-f0a0d23ae543
-- title:
--   Is MCS: exists var mem of witnessed
-- statement:
--   Every witnessed MCS contains an element-variable pattern.  This is the
--   source's Existence rule followed by the MCS's witness implication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L73-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean#L73-L81

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCanonicalCore

theorem MatchingLogic.IsMCS.exists_var_mem_of_witnessed
    {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma) (hW : Witnessed Gamma) :
    ∃ y : Nat, Pattern.var y ∈ Gamma := by sorry
