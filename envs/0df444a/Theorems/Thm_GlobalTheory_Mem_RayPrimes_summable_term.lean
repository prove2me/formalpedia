-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayPrimes_summable_term
-- name    : GlobalTheory.Mem.RayPrimes.summable_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:43.697242+00:00
-- url     : https://prove2.me/theorems/7687fc30-f00f-4375-b175-ab1966b09843
-- title:
--   Ray Primes: summable term
-- statement:
--   The Ray Primes construction uses the summable term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L101-L103

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
variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha

theorem GlobalTheory.Mem.RayPrimes.summable_term (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) := by sorry
