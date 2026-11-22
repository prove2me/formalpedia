-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_roundtrip
-- name    : MatchingLogic.Pattern.substVar_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:44.83649+00:00
-- url     : https://prove2.me/theorems/3fa9bda6-c8a6-41ff-9ea7-1d3bf7f8a317
-- title:
--   Pattern: subst Var roundtrip
-- statement:
--   Replacing `x` by a wholly fresh `y`, then `y` by `x`, is literally the
--   original raw pattern.  No quotient by alpha equivalence is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L56-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Alpha.lean#L56-L87

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

theorem MatchingLogic.Pattern.substVar_roundtrip {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    substVar y x (substVar x y p) = p := by sorry
