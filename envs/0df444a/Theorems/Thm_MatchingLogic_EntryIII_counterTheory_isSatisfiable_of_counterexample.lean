-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_counterTheory_isSatisfiable_of_counterexample
-- name    : MatchingLogic.EntryIII.counterTheory_isSatisfiable_of_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:22.365255+00:00
-- url     : https://prove2.me/theorems/37010a32-d416-44fa-8804-6338adf902ca
-- title:
--   Entry III: counter Theory is Satisfiable of counterexample
-- statement:
--   Conversely, a matching counterexample yields a model of the FOL
--   counterexample theory.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L301-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L301-L325

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

theorem MatchingLogic.EntryIII.counterTheory_isSatisfiable_of_counterexample
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (M : Model S) (rho : Var → M.carrier) (u : M.carrier)
    (hDelta : u ∈ M.denoteSet rho Delta) (hphi : u ∉ M.denote rho phi) :
    FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by sorry
