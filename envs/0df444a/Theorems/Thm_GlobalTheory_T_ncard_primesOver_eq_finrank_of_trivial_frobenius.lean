-- Prove2me | Theorems.Thm_GlobalTheory_T_ncard_primesOver_eq_finrank_of_trivial_frobenius
-- name    : GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:54:09.760987+00:00
-- url     : https://prove2.me/theorems/19b33502-d14a-43ae-8f0f-7c2eb7a075cf
-- title:
--   T: ncard primes Over eq finrank of trivial frobenius
-- statement:
--   The T construction uses the ncard primes Over eq finrank of trivial frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobenius
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) → (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧ ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by sorry
