-- Prove2me | Theorems.Thm_MatchingLogic_Model_step_iff_exists_coord
-- name    : MatchingLogic.Model.step_iff_exists_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:34.353868+00:00
-- url     : https://prove2.me/theorems/994aea8b-2185-4bc0-9b59-bc29f7b19594
-- title:
--   Model: step iff exists coord
-- statement:
--   `⇝` of Definition 2 is the union of the `⇝_e` over all coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L78-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L78-L84

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

theorem MatchingLogic.Model.step_iff_exists_coord (u v : M.carrier) :
    M.Step u v ↔ ∃ e : Coord S, M.stepAt e u v := by sorry
