-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_mono
-- name    : MatchingLogic.LocProvable.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:45.24926+00:00
-- url     : https://prove2.me/theorems/9f7dad1a-f6ca-40b5-aa78-c73e92601d7e
-- title:
--   Loc Provable: mono
-- statement:
--   The Loc Provable construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L242-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L242-L245

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

theorem MatchingLogic.LocProvable.mono {Gamma Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGD : Gamma ⊆ Delta) (h : LocProvable Gamma phi) : LocProvable Delta phi := by sorry
