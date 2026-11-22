-- Prove2me | Theorems.Thm_MatchingLogic_Provable_or_intro_right
-- name    : MatchingLogic.Provable.or_intro_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:01.576261+00:00
-- url     : https://prove2.me/theorems/008e3b59-beb3-48a9-9e05-6f6cadf92637
-- title:
--   Provable: or intro right
-- statement:
--   Right disjunction introduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L118-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean#L118-L122

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

theorem MatchingLogic.Provable.or_intro_right (Gamma : Set (Pattern S Var)) (phi psi : Pattern S Var) :
    Provable Gamma (.imp psi (Pattern.or phi psi)) := by sorry
