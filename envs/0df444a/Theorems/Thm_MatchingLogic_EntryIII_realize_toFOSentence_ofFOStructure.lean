-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_realize_toFOSentence_ofFOStructure
-- name    : MatchingLogic.EntryIII.realize_toFOSentence_ofFOStructure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:12.58957+00:00
-- url     : https://prove2.me/theorems/5fbd9b6a-66e9-4290-8451-160c84fbb5a1
-- title:
--   Entry III: realize to FOSentence of FOStructure
-- statement:
--   Correctness in an arbitrary structure of the constants-expanded language,
--   after recovering its matching model, valuation, and current point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L248-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L248-L265

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

theorem MatchingLogic.EntryIII.realize_toFOSentence_ofFOStructure (A : Type) [Nonempty A]
    [(relLanguage S)[[Option Var]].Structure A] (p : Pattern S Var) :
    A ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      Model.ofFOCurrent (S := S) (Var := Var) A ∈
        (Model.ofFOStructure (S := S) (Var := Var) A).denote
          (Model.ofFOValuation (S := S) (Var := Var) A) p := by sorry
