-- Prove2me | Theorems.Thm_MatchingLogic_EntryIII_realize_toFOAux_of_rel
-- name    : MatchingLogic.EntryIII.realize_toFOAux_of_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:48.153806+00:00
-- url     : https://prove2.me/theorems/d769f39b-2b17-4ff9-af21-e3ebac9a5354
-- title:
--   Entry III: realize to FOAux of rel
-- statement:
--   Correctness of the open-formula translation for any relational structure
--   whose relation maps agree with a matching-logic model.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L107-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Compactness.lean#L107-L195

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

theorem MatchingLogic.EntryIII.realize_toFOAux_of_rel (M : Model S) [(relLanguage S).Structure M.carrier]
    (hcompat : ∀ (sigma : S.Sym) (out : M.carrier)
      (args : Fin (S.arity sigma) → M.carrier),
      FirstOrder.Language.Structure.RelMap (relSym sigma) (Fin.cons out args) ↔
        out ∈ M.interp sigma args)
    (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    FirstOrder.Language.Formula.Realize
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by sorry
