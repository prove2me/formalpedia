-- Prove2me | Theorems.Thm_MatchingLogic_denote_dia
-- name    : MatchingLogic.denote_dia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:42.556501+00:00
-- url     : https://prove2.me/theorems/2eeb9064-0ba1-4e6b-b5f3-8dd1f673a1ca
-- title:
--   Matching Logic: denote dia
-- statement:
--   The denotation of `⟨e⟩ψ`: the points with an `e`-successor in `ψ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L113-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L113-L125

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

theorem MatchingLogic.denote_dia (M : Model S) (ρ : Var → M.carrier) (e : Coord S)
    (ψ : Pattern S Var) :
    M.denote ρ (dia e ψ) = {u | ∃ v, M.stepAt e u v ∧ v ∈ M.denote ρ ψ} := by sorry
