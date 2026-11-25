-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_of_specializes
-- name    : GlobalTheory.exists_complete_discreteValuationRing_of_specializes
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:32.682217+00:00
-- url     : https://prove2.me/theorems/0db44dc5-e22a-4bda-9f38-e465965c2584
-- title:
--   Global Theory: exists complete discrete Valuation Ring of specializes
-- statement:
--   The Global Theory construction uses the exists complete discrete Valuation Ring of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L680-L702
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L680-L702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.exists_complete_discreteValuationRing_of_specializes {X : Scheme.{u}}
    [IsLocallyNoetherian X] {η x : X} (h : η ⤳ x) (hne : η ≠ x) :
    ∃ (O : CommRingCat.{u}) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (f : Spec O ⟶ X),
      f (⊥ : PrimeSpectrum O) = η ∧ f (closedPoint O) = x := by sorry
