-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayPrimes_eq_span_of_not_prime
-- name    : GlobalTheory.Mem.RayPrimes.eq_span_of_not_prime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:25:03.531861+00:00
-- url     : https://prove2.me/theorems/f0e294b6-60af-4f92-a028-8b89ee572be6
-- title:
--   Ray Primes: eq span of not prime
-- statement:
--   The Ray Primes construction uses the eq span of not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L241-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L241-L272

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

theorem GlobalTheory.Mem.RayPrimes.eq_span_of_not_prime (h2 : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by sorry
