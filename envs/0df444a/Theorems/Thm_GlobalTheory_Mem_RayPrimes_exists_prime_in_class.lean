-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayPrimes_exists_prime_in_class
-- name    : GlobalTheory.Mem.RayPrimes.exists_prime_in_class
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:54.840301+00:00
-- url     : https://prove2.me/theorems/1896336c-b6b7-4af5-a4c1-6e77bc0ff284
-- title:
--   Ray Primes: exists prime in class
-- statement:
--   The Ray Primes construction uses the exists prime in class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L296-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L296-L324

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

theorem GlobalTheory.Mem.RayPrimes.exists_prime_in_class : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by sorry
