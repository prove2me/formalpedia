-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_inv_absNorm_primes_of_not_prime_norm
-- name    : GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:00:07.525106+00:00
-- url     : https://prove2.me/theorems/dc61eae1-b75e-4f2e-a429-ae23f751323f
-- title:
--   T: summable inv abs Norm primes of not prime norm
-- statement:
--   The T construction uses the summable inv abs Norm primes of not prime norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SummableInvAbsNormPrimesOfNotPrimeNormStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SummableInvAbsNormPrimesOfNotPrimeNormStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm : ∀ (K : Type) [Field K] [NumberField K], Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} => ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by sorry
