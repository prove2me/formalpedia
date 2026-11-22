-- Prove2me | Theorems.Thm_MatchingLogic_Provable_or_intro_left
-- name    : MatchingLogic.Provable.or_intro_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:01.527882+00:00
-- url     : https://prove2.me/theorems/b38d88cd-659c-4f65-bff6-24349c15ddb7
-- title:
--   Provable: or intro left
-- statement:
--   Left disjunction introduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L106-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L106-L110

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

theorem MatchingLogic.Provable.or_intro_left (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp phi (Pattern.or phi psi)) := by sorry
