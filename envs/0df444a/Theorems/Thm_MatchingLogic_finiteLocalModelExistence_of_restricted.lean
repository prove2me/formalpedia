-- Prove2me | Theorems.Thm_MatchingLogic_finiteLocalModelExistence_of_restricted
-- name    : MatchingLogic.finiteLocalModelExistence_of_restricted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:57.986807+00:00
-- url     : https://prove2.me/theorems/2aed6d9d-c7d0-4605-a3a8-e826feac8ff2
-- title:
--   Matching Logic: finite Local Model Existence of restricted
-- statement:
--   Finite pointed-model existence for every finite sub-signature implies
--   finite pointed-model existence for the ambient signature.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L207-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureReduction.lean#L207-L228

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.finiteLocalModelExistence_of_restricted
    (hmodel : ∀ F : Finset S.Sym, FiniteLocalModelExistence (S.restrict F) Nat) :
    FiniteLocalModelExistence S Nat := by sorry
