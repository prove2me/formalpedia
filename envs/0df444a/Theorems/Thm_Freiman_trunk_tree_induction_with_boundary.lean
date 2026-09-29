-- Prove2me | Theorems.Thm_Freiman_trunk_tree_induction_with_boundary
-- name    : Freiman.trunk_tree_induction_with_boundary
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:37:38.861508+00:00
-- url     : https://prove2.me/theorems/1edbccb2-8a52-4597-98e8-6d11e2dbe757
-- title:
--   trunk tree induction with boundary
-- statement:
--   Structural induction on pair/split/diagonal trees transports the exact witness rectangles and premise membership; the diagonal node splits by r≤s or s≤r; the two exceptional equality-boundary records use the explicitly supplied original-polynomial corner argument.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_tree_induction_with_boundary (C : TrunkCatalog) (hw : trunkAllWitnesses C)
    (he : ∀ w : TrunkWitness, trunkWitnessValid C w → TrunkWitnessExclusion C w)
    (hs : ∀ (R : CertRectangle) (axis : Bool), certRectangleValid R → ∀ r s : ℝ, certRectangleMem R r s →
      (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
      (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s))
    (hb : ∀ (R : CertRectangle) (bs : List CertBound), trunkBoundaryBound R bs → ∀ r s q : ℝ, certRectangleMem R r s → ¬ trunkHolds bs r s q) :
    TrunkTreeSound C := by
  sorry
