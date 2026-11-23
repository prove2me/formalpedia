-- Prove2me | Theorems.Thm_GlobalTheory_summable_inv_absNorm_of_not_prime
-- name    : GlobalTheory.summable_inv_absNorm_of_not_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:37.452605+00:00
-- url     : https://prove2.me/theorems/210e8dca-43be-406a-b0c0-a6d0b7f2611a
-- title:
--   Global Theory: summable inv abs Norm of not prime
-- statement:
--   The Global Theory construction uses the summable inv abs Norm of not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SummableInvAbsNormPrimesOfNotPrimeNorm.lean#L37-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SummableInvAbsNormPrimesOfNotPrimeNorm.lean#L37-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
open GlobalTheory
open NumberField IsDedekindDomain
open scoped Classical

theorem GlobalTheory.summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by sorry
