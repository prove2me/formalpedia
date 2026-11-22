-- Prove2me | Theorems.Thm_MatchingLogic_Model_reachWord_nil
-- name    : MatchingLogic.Model.reachWord_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:12.814541+00:00
-- url     : https://prove2.me/theorems/65f86d1f-b473-4d57-a94f-004f4311a9ae
-- title:
--   Model: reach Word nil
-- statement:
--   The Model construction uses the reach Word nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L72-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L72-L72

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

theorem MatchingLogic.Model.reachWord_nil (u v : M.carrier) : M.reachWord [] u v ↔ u = v := by sorry
