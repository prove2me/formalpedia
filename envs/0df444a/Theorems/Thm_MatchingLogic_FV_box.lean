-- Prove2me | Theorems.Thm_MatchingLogic_FV_box
-- name    : MatchingLogic.FV_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:17.57287+00:00
-- url     : https://prove2.me/theorems/ef99ee1a-228a-488e-b567-715c4c8b9aee
-- title:
--   Matching Logic: FV box
-- statement:
--   The Matching Logic construction uses the FV box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L194-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L194-L195

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

theorem MatchingLogic.FV_box (e : Coord S) (ψ : Pattern S Var) : FV (box e ψ) = FV ψ := by sorry
