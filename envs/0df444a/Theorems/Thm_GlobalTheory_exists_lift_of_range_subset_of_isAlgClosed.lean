-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_of_range_subset_of_isAlgClosed
-- name    : GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:03.226097+00:00
-- url     : https://prove2.me/theorems/1fd1d5d2-3fa2-490c-add1-b2a7228a9654
-- title:
--   Global Theory: exists lift of range subset of is Alg Closed
-- statement:
--   The Global Theory construction uses the exists lift of range subset of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftAlgebraicallyClosedPoint.lean#L6-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftAlgebraicallyClosedPoint.lean#L6-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f]
      (k : Type) [Field k] [IsAlgClosed k]
      (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
      ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by sorry
