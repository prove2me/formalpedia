-- Prove2me | Theorems.Thm_MatchingLogic_Model_reachWord_append
-- name    : MatchingLogic.Model.reachWord_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:32.572838+00:00
-- url     : https://prove2.me/theorems/175497c8-ddde-4899-acda-663c69a7d4cc
-- title:
--   Model: reach Word append
-- statement:
--   The Model construction uses the reach Word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L214-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L214-L225

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

theorem MatchingLogic.Model.reachWord_append (M : Model S) (p q : List (Coord S)) (u v : M.carrier) :
    M.reachWord (p ++ q) u v ↔ ∃ w, M.reachWord p u w ∧ M.reachWord q w v := by sorry
