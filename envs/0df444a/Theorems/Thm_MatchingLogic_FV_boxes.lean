-- Prove2me | Theorems.Thm_MatchingLogic_FV_boxes
-- name    : MatchingLogic.FV_boxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:14.002803+00:00
-- url     : https://prove2.me/theorems/83a580c9-0cab-4c5d-9dba-5995c4e91999
-- title:
--   Matching Logic: FV boxes
-- statement:
--   The Matching Logic construction uses the FV boxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L197-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L197-L201

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

theorem MatchingLogic.FV_boxes (p : List (Coord S)) (ψ : Pattern S Var) :
    FV (boxes p ψ) = FV ψ := by sorry
