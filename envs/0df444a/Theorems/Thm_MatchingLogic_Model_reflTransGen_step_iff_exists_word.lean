-- Prove2me | Theorems.Thm_MatchingLogic_Model_reflTransGen_step_iff_exists_word
-- name    : MatchingLogic.Model.reflTransGen_step_iff_exists_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:36.498801+00:00
-- url     : https://prove2.me/theorems/c0fdf221-f10e-42d2-bf89-46c76a7958f0
-- title:
--   Model: refl Trans Gen step iff exists word
-- statement:
--   `⇝*` is reachability along some word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L87-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L87-L104

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

theorem MatchingLogic.Model.reflTransGen_step_iff_exists_word (u v : M.carrier) :
    Relation.ReflTransGen M.Step u v ↔ ∃ p : List (Coord S), M.reachWord p u v := by sorry
