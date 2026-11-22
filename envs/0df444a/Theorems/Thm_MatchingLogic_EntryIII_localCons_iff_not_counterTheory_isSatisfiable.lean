-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_localCons_iff_not_counterTheory_isSatisfiable
-- name    : MatchingLogic.EntryIII.localCons_iff_not_counterTheory_isSatisfiable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:32.733107+00:00
-- url     : https://prove2.me/theorems/56727239-253e-4637-ae47-a15e33022bef
-- title:
--   Entry III: local Cons iff not counter Theory is Satisfiable
-- statement:
--   Exact semantic equivalence used by the compactness reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L328-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L328-L335

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.ModelTheory.Satisfiability
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIII
open FirstOrder
universe u
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.EntryIII.localCons_iff_not_counterTheory_isSatisfiable
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by sorry
