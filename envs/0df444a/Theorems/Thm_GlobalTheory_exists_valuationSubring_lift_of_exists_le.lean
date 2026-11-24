-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_exists_le
-- name    : GlobalTheory.exists_valuationSubring_lift_of_exists_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:19.890386+00:00
-- url     : https://prove2.me/theorems/9adea172-04ed-46a8-893f-5f1f656fa037
-- title:
--   Global Theory: exists valuation Subring lift of exists le
-- statement:
--   The Global Theory construction uses the exists valuation Subring lift of exists le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L187-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L187-L233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
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
universe u

theorem GlobalTheory.exists_valuationSubring_lift_of_exists_le {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A]
    (m : Ideal A) [hm : m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U := by sorry
