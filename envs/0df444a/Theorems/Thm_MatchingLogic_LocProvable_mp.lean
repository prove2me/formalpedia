-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_mp
-- name    : MatchingLogic.LocProvable.mp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:10.180663+00:00
-- url     : https://prove2.me/theorems/b6827af3-8c04-4bb6-9661-e1a78ae46059
-- title:
--   Loc Provable: mp
-- statement:
--   The Loc Provable construction uses the mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L277-L288
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L277-L288

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

theorem MatchingLogic.LocProvable.mp {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : LocProvable Gamma phi) (himp : LocProvable Gamma (.imp phi psi)) :
    LocProvable Gamma psi := by sorry
