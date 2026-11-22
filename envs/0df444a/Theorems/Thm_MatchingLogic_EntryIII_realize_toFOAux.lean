-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_realize_toFOAux
-- name    : MatchingLogic.EntryIII.realize_toFOAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:11.291171+00:00
-- url     : https://prove2.me/theorems/33895371-1134-4ed4-83ee-fbbd82a41f14
-- title:
--   Entry III: realize to FOAux
-- statement:
--   Correctness specialized to the FOL structure built from a matching model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L198-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L198-L207

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

theorem MatchingLogic.EntryIII.realize_toFOAux (M : Model S) (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    @FirstOrder.Language.Formula.Realize (relLanguage S) M.carrier
        (Model.toFOStructure M) alpha
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by sorry
