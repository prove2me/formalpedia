-- Prove2me | Theorems.Thm_MatchingLogic_locProvable_empty_iff
-- name    : MatchingLogic.locProvable_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:33.809497+00:00
-- url     : https://prove2.me/theorems/fe6673e3-5739-4c59-946f-083fb250c689
-- title:
--   Matching Logic: loc Provable empty iff
-- statement:
--   Source Proposition 3.5(3), in the repository's finite-list presentation:
--   local and ordinary theoremhood coincide for the empty theory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Countertheory.lean#L43-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Countertheory.lean#L43-L54

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

theorem MatchingLogic.locProvable_empty_iff {phi : Pattern S Var} :
    LocProvable (∅ : Set (Pattern S Var)) phi ↔
      Provable (∅ : Set (Pattern S Var)) phi := by sorry
