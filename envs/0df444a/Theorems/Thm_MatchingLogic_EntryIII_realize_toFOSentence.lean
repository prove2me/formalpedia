-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_realize_toFOSentence
-- name    : MatchingLogic.EntryIII.realize_toFOSentence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:14.041076+00:00
-- url     : https://prove2.me/theorems/32705f5f-acb7-4501-a997-d943f0a5343d
-- title:
--   Entry III: realize to FOSentence
-- statement:
--   Correctness of sentence translation in the constants expansion built from a
--   matching model, valuation, and current point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L217-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L217-L244

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

theorem MatchingLogic.EntryIII.realize_toFOSentence (M : Model S) (rho : Var → M.carrier)
    (u : M.carrier) (p : Pattern S Var) :
    letI : (relLanguage S).Structure M.carrier := Model.toFOStructure M
    letI : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
      FirstOrder.Language.constantsOn.structure
        (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
    M.carrier ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      u ∈ M.denote rho p := by sorry
