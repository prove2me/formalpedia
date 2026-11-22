-- Prove2me | Theorems.Thm_MatchingLogic_boxes_cons
-- name    : MatchingLogic.boxes_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:12.179609+00:00
-- url     : https://prove2.me/theorems/ab83c4f5-db1c-4dde-a06a-e69e53903476
-- title:
--   Matching Logic: boxes cons
-- statement:
--   The Matching Logic construction uses the boxes cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L55-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L55-L56

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

theorem MatchingLogic.boxes_cons (e : Coord S) (p : List (Coord S)) (ψ : Pattern S Var) :
    boxes (e :: p) ψ = box e (boxes p ψ) := by sorry

attribute [defeq] MatchingLogic.boxes_cons
