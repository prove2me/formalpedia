-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_not_counterTheory_isSatisfiable
-- name    : MatchingLogic.EntryIII.not_counterTheory_isSatisfiable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:19.888714+00:00
-- url     : https://prove2.me/theorems/3e99aa32-64c3-4248-8931-72a5323470c2
-- title:
--   Entry III: not counter Theory is Satisfiable
-- statement:
--   A local semantic consequence has no FOL countermodel under the translation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L274-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L274-L297

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

theorem MatchingLogic.EntryIII.not_counterTheory_isSatisfiable {Delta : Set (Pattern S Var)}
    {phi : Pattern S Var} (hlocal : LocalCons Delta phi) :
    ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by sorry
