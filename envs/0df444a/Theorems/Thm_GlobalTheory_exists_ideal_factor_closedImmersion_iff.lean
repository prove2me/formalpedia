-- Prove2me | Theorems.Thm_GlobalTheory_exists_ideal_factor_closedImmersion_iff
-- name    : GlobalTheory.exists_ideal_factor_closedImmersion_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:12.638704+00:00
-- url     : https://prove2.me/theorems/1a0b11d3-5825-413a-97f4-2293aed58b95
-- title:
--   Global Theory: exists ideal factor closed Immersion iff
-- statement:
--   The Global Theory construction uses the exists ideal factor closed Immersion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingPointsIdealCriterion.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalRingPointsIdealCriterion.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterion
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

theorem GlobalTheory.exists_ideal_factor_closedImmersion_iff (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by sorry
