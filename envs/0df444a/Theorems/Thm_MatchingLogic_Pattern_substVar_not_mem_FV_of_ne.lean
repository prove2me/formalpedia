-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_not_mem_FV_of_ne
-- name    : MatchingLogic.Pattern.substVar_not_mem_FV_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:42.251614+00:00
-- url     : https://prove2.me/theorems/3f485989-31ce-4ae1-9830-90b9a7e69a8b
-- title:
--   Pattern: subst Var not mem FV of ne
-- statement:
--   A variable distinct from the replacement and absent from the source remains
--   absent after raw variable substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L42-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L42-L63

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.substVar_not_mem_FV_of_ne {x y z : Nat}
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (substVar x y p) := by sorry
