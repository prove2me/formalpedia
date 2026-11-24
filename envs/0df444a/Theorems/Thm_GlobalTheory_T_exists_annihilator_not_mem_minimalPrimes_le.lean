-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_annihilator_not_mem_minimalPrimes_le
-- name    : GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:28.817678+00:00
-- url     : https://prove2.me/theorems/8cb6dd11-9096-4390-9b60-0a660ef6aa9d
-- title:
--   T: exists annihilator not mem minimal Primes le
-- statement:
--   The T construction uses the exists annihilator not mem minimal Primes le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnnihilatorAvoidsFibreMinimalPrimesStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnnihilatorAvoidsFibreMinimalPrimesStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimesStatement
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

theorem GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B),
    (∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) →
    ∀ u : PrimeSpectrum B, ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by sorry
