-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_localization_eq_zero_of_mul_eq_zero
-- name    : GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:15.362174+00:00
-- url     : https://prove2.me/theorems/17a1a887-7969-44db-ba25-8ee9188c0680
-- title:
--   Flat Fibre Regular: localization eq zero of mul eq zero
-- statement:
--   The Flat Fibre Regular construction uses the localization eq zero of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L191-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L191-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular

theorem GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by sorry
