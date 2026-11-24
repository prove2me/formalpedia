-- Prove2me | Theorems.Thm_GlobalTheory_annihilator_avoids_fibre_minimalPrimes
-- name    : GlobalTheory.annihilator_avoids_fibre_minimalPrimes
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:40.536701+00:00
-- url     : https://prove2.me/theorems/8978c7b1-1e6c-4bc4-b573-104b19d5ea52
-- title:
--   Global Theory: annihilator avoids fibre minimal Primes
-- statement:
--   The Global Theory construction uses the annihilator avoids fibre minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnnihilatorAvoidsFibreMinimalPrimes.lean#L6-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnnihilatorAvoidsFibreMinimalPrimes.lean#L6-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by sorry
