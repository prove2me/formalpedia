-- Prove2me | Theorems.Thm_MatchingLogic_boxes_append
-- name    : MatchingLogic.boxes_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:32.147359+00:00
-- url     : https://prove2.me/theorems/e6461fd7-668e-4d31-bbe0-64aa1867f62e
-- title:
--   Matching Logic: boxes append
-- statement:
--   The Matching Logic construction uses the boxes append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L208-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L208-L212

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

theorem MatchingLogic.boxes_append (p q : List (Coord S)) (ψ : Pattern S Var) :
    boxes (p ++ q) ψ = boxes p (boxes q ψ) := by sorry
