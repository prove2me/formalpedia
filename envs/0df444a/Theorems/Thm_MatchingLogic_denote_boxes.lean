-- Prove2me | Theorems.Thm_MatchingLogic_denote_boxes
-- name    : MatchingLogic.denote_boxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:43.213414+00:00
-- url     : https://prove2.me/theorems/ac8fe19c-dbf9-4a91-8c20-33d38dc4cca9
-- title:
--   Matching Logic: denote boxes
-- statement:
--   **Lemma 4 (box semantics).**  `⟦[p]ψ⟧ = {u | ⇝_p[u] ⊆ ⟦ψ⟧}`.
--
--   The paper states this for closed `ψ`, because it writes both sides with `⟦·⟧`.
--   No closedness hypothesis is needed here, and the reason is `FV_boxes` below:
--   `dia`, `box` and `boxes` are binder-free, so `FV ([p]ψ) = FV ψ` exactly and both
--   sides read ψ's free variables off the same `ρ`.  (Merely "both sides carry the
--   same valuation" would NOT suffice -- a box that introduced a binder would
--   evaluate ψ under an updated valuation on the left and not on the right.)
--   Instantiating at a closed `ψ` recovers the paper's statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L152-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Boxes.lean#L152-L170

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

theorem MatchingLogic.denote_boxes (M : Model S) (ρ : Var → M.carrier) (p : List (Coord S))
    (ψ : Pattern S Var) :
    M.denote ρ (boxes p ψ) = {u | ∀ v, M.reachWord p u v → v ∈ M.denote ρ ψ} := by sorry
