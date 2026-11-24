-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayPrimes_summable_of_not_prime_or_le
-- name    : GlobalTheory.Mem.RayPrimes.summable_of_not_prime_or_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:09.293857+00:00
-- url     : https://prove2.me/theorems/d99782af-b17f-4069-9b24-099d4eb03fa1
-- title:
--   Ray Primes: summable of not prime or le
-- statement:
--   The Ray Primes construction uses the summable of not prime or le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L274-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L274-L292

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
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
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.RayPrimes.summable_of_not_prime_or_le (h2 : Module.finrank ℚ K = 2) (N : ℕ) {ι : Type}
    (f : ι → HeightOneSpectrum (𝓞 K)) (hf : Function.Injective f)
    (h : ∀ i, (Ideal.absNorm (f i).asIdeal).Prime → Ideal.absNorm (f i).asIdeal ≤ N) :
    Summable fun i => ((Ideal.absNorm (f i).asIdeal : ℕ) : ℝ)⁻¹ := by sorry
