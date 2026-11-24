-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem
-- name    : GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:44.260511+00:00
-- url     : https://prove2.me/theorems/1c422354-ccdd-4d29-ab01-c64ddfca3e07
-- title:
--   Global Theory: exists finite ncard primes Over eq finrank of pow abs Norm sub mem
-- statement:
--   The Global Theory construction uses the exists finite ncard primes Over eq finrank of pow abs Norm sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardPrimesOverEqFinrankOfTrivialFrobenius.lean#L26-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardPrimesOverEqFinrankOfTrivialFrobenius.lean#L26-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory

theorem GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by sorry
