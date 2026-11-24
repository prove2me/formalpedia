-- Prove2me | Theorems.Thm_GlobalTheory_Mem_NormPrimes_exists_prime_norm
-- name    : GlobalTheory.Mem.NormPrimes.exists_prime_norm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:30.856163+00:00
-- url     : https://prove2.me/theorems/a2f76b5c-902a-4e0b-b408-5c413890d39e
-- title:
--   Norm Primes: exists prime norm
-- statement:
--   The Norm Primes construction uses the exists prime norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeElementCongruent.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeElementCongruent.lean#L68-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonemptyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeElementCongruent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.NormPrimes

theorem GlobalTheory.Mem.NormPrimes.exists_prime_norm : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by sorry
