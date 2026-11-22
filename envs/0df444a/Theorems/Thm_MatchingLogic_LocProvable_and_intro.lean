-- Prove2me | Theorems.Thm_MatchingLogic_LocProvable_and_intro
-- name    : MatchingLogic.LocProvable.and_intro
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:12.787995+00:00
-- url     : https://prove2.me/theorems/df16603c-33bb-4d11-ba87-3bb1559adc77
-- title:
--   Loc Provable: and intro
-- statement:
--   The Loc Provable construction uses the and intro property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L290-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L290-L301

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Theorems.Thm_MatchingLogic_Provable_and_intro

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternLocalTheory
attribute [local instance] instDecidableEqPatternLocalTheory
open MatchingLogic.LocProvable

theorem MatchingLogic.LocProvable.and_intro {Gamma : Set (Pattern S Var)} {phi psi : Pattern S Var}
    (hphi : LocProvable Gamma phi) (hpsi : LocProvable Gamma psi) :
    LocProvable Gamma (Pattern.and phi psi) := by sorry
