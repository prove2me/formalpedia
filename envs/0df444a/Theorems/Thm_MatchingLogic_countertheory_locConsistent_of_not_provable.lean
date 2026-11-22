-- Prove2me | Theorems.Thm_MatchingLogic_countertheory_locConsistent_of_not_provable
-- name    : MatchingLogic.countertheory_locConsistent_of_not_provable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:53.690073+00:00
-- url     : https://prove2.me/theorems/4f9c993e-a010-4bb7-858e-979f2878316b
-- title:
--   Matching Logic: countertheory loc Consistent of not provable
-- statement:
--   If `conj l → phi` is not a theorem, then the finite countertheory consisting
--   of `conj l` and `¬phi` is locally consistent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Countertheory.lean#L66-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Countertheory.lean#L66-L90

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.countertheory_locConsistent_of_not_provable
    {l : List (Pattern S Var)} {phi : Pattern S Var}
    (hnot : ¬ Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)) :
    LocConsistent {delta | delta ∈ [conj l, Pattern.nt phi]} := by sorry
