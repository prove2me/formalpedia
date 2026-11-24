-- Prove2me | Theorems.Thm_GlobalTheory_CyclotomicPrimes_exists_prime_absNorm_eq_of_irreducible_cyclotomic
-- name    : GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:57.605201+00:00
-- url     : https://prove2.me/theorems/29e0b71b-b32b-43a5-805d-17f1b9ae6df1
-- title:
--   Cyclotomic Primes: exists prime abs Norm eq of irreducible cyclotomic
-- statement:
--   The Cyclotomic Primes construction uses the exists prime abs Norm eq of irreducible cyclotomic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomic.lean#L20-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomic.lean#L20-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
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
open GlobalTheory GlobalTheory.CyclotomicPrimes

theorem GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by sorry
