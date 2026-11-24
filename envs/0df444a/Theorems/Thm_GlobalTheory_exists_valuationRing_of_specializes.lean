-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationRing_of_specializes
-- name    : GlobalTheory.exists_valuationRing_of_specializes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:49.31095+00:00
-- url     : https://prove2.me/theorems/075d51f0-2fcc-4a82-af8f-be84b05a4080
-- title:
--   Global Theory: exists valuation Ring of specializes
-- statement:
--   The Global Theory construction uses the exists valuation Ring of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationRingDominatingSpecialization.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationRingDominatingSpecialization.lean#L10-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecialization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.exists_valuationRing_of_specializes (X : Scheme.{0}) (x' x : X) (h : x' ⤳ x) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V)
      (g : Spec (CommRingCat.of V) ⟶ X),
      g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by sorry
