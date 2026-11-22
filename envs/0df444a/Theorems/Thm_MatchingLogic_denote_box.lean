-- Prove2me | Theorems.Thm_MatchingLogic_denote_box
-- name    : MatchingLogic.denote_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:42.18597+00:00
-- url     : https://prove2.me/theorems/222061db-afb3-4791-8371-0bf198bbbe93
-- title:
--   Matching Logic: denote box
-- statement:
--   Auxiliary: the denotation of `[e]ψ` is the points all of whose `e`-successors
--   lie in `⟦ψ⟧`.  This is the complement step of the paper's proof of Lemma 4,
--   factored out so the word induction below only has to compose it with itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L130-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L130-L141

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
variable [DecidableEq Var]

theorem MatchingLogic.denote_box (M : Model S) (ρ : Var → M.carrier) (e : Coord S)
    (ψ : Pattern S Var) :
    M.denote ρ (box e ψ) = {u | ∀ v, M.stepAt e u v → v ∈ M.denote ρ ψ} := by sorry
