-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_source_not_mem_FV
-- name    : MatchingLogic.Pattern.substVar_source_not_mem_FV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:18.782297+00:00
-- url     : https://prove2.me/theorems/30bb7baf-a562-43a9-bc22-6db6841b3c28
-- title:
--   Pattern: subst Var source not mem FV
-- statement:
--   If source and replacement differ, no free source occurrence remains after
--   variable-for-variable substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L137-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L137-L157

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.substVar_source_not_mem_FV {x y : Nat} (p : Pattern S Nat)
    (hxy : x ≠ y) : x ∉ FV (substVar x y p) := by sorry
