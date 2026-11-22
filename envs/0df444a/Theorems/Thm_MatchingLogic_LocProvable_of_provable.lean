-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_of_provable
-- name    : MatchingLogic.LocProvable.of_provable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:53.833528+00:00
-- url     : https://prove2.me/theorems/c8b99ab7-f15a-40e1-9c50-6682be224325
-- title:
--   Loc Provable: of provable
-- statement:
--   The Loc Provable construction uses the of provable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L255-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L255-L259

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.LocProvable

theorem MatchingLogic.LocProvable.of_provable {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable (∅ : Set (Pattern S Var)) phi) : LocProvable Gamma phi := by sorry
