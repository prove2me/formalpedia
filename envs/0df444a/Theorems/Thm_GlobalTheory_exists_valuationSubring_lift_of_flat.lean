-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_flat
-- name    : GlobalTheory.exists_valuationSubring_lift_of_flat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:26.543419+00:00
-- url     : https://prove2.me/theorems/6d7e006b-9c2d-40d6-8420-4f3884e4f2fa
-- title:
--   Global Theory: exists valuation Subring lift of flat
-- statement:
--   The Global Theory construction uses the exists valuation Subring lift of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L260-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L260-L272

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

theorem GlobalTheory.exists_valuationSubring_lift_of_flat {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (m : Ideal A) [m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U := by sorry
