-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal
-- name    : GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:39.549407+00:00
-- url     : https://prove2.me/theorems/2d0a39c1-b1ff-4c43-8ee6-2cc66d81314e
-- title:
--   T: smooth algebra localization eq zero of avoid fibre minimal
-- statement:
--   The T construction uses the smooth algebra localization eq zero of avoid fibre minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by sorry
