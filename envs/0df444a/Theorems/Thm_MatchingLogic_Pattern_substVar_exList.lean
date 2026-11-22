-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_substVar_exList
-- name    : MatchingLogic.Pattern.substVar_exList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:19.316896+00:00
-- url     : https://prove2.me/theorems/e05d29b4-3fa4-40d0-b1d8-bce697b69abf
-- title:
--   Pattern: subst Var ex List
-- statement:
--   Raw substitution commutes with a list of existential binders when its
--   source is distinct from every binder.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L67-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessPush.lean#L67-L75

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

theorem MatchingLogic.Pattern.substVar_exList {a b : Nat} (ys : List Nat) (p : Pattern S Nat)
    (ha : ∀ y ∈ ys, a ≠ y) :
    substVar a b (exList ys p) = exList ys (substVar a b p) := by sorry
