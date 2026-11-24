-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayPrimes_not_summable_class
-- name    : GlobalTheory.Mem.RayPrimes.not_summable_class
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:54.801652+00:00
-- url     : https://prove2.me/theorems/1a6579b7-5c77-456a-8ce7-f718b8e8d47a
-- title:
--   Ray Primes: not summable class
-- statement:
--   The Ray Primes construction uses the not summable class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L155-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean#L155-L226

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
variable {G : Type} [CommGroup G] [Fintype G]

theorem GlobalTheory.Mem.RayPrimes.not_summable_class {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (cl : ι → G)
    (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s))
    (hχ : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      cexp (∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))) = L s)
    (Z : ℂ → ℂ) (hZ : Continuous Z) (hZ1 : Z 1 ≠ 0)
    (h1 : ∀ s : ℝ, 1 < s → Z s = (s - 1) *
      cexp (∑' v, -log (1 - ((1 : G →* ℂˣ) (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))))
    (c : G) : ¬ Summable fun v : {v // cl v = c} => (n v : ℝ)⁻¹ := by sorry
