-- Prove2me | Theorems.Thm_MatchingLogic_Model_reachWord_cons
-- name    : MatchingLogic.Model.reachWord_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:11.373579+00:00
-- url     : https://prove2.me/theorems/19c26a42-52b2-4f0c-a7c1-80a552b29b58
-- title:
--   Model: reach Word cons
-- statement:
--   The Model construction uses the reach Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L74-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L74-L75

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type}
open MatchingLogic.Model
variable (M : Model S)

theorem MatchingLogic.Model.reachWord_cons (e : Coord S) (p : List (Coord S)) (u v : M.carrier) :
    M.reachWord (e :: p) u v ↔ ∃ w, M.stepAt e u w ∧ M.reachWord p w v := by sorry
