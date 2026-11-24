-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_valuationRing_dominating_specialization
-- name    : GlobalTheory.T.exists_valuationRing_dominating_specialization
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:38:17.001389+00:00
-- url     : https://prove2.me/theorems/13686cc5-d14f-4c5e-80f1-ac9399ac3c60
-- title:
--   T: exists valuation Ring dominating specialization
-- statement:
--   The T construction uses the exists valuation Ring dominating specialization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationRingDominatingSpecializationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationRingDominatingSpecializationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecialization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecializationStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_valuationRing_dominating_specialization : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by sorry
