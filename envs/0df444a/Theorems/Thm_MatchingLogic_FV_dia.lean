-- Prove2me | Theorems.Thm_MatchingLogic_FV_dia
-- name    : MatchingLogic.FV_dia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:14.651659+00:00
-- url     : https://prove2.me/theorems/d35b4537-8c57-4a8f-a9b1-d895e6bcdc01
-- title:
--   Matching Logic: FV dia
-- statement:
--   The Matching Logic construction uses the FV dia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L182-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L182-L192

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

theorem MatchingLogic.FV_dia (e : Coord S) (ψ : Pattern S Var) : FV (dia e ψ) = FV ψ := by sorry
