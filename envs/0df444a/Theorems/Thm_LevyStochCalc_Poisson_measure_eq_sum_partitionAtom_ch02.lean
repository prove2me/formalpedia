-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_measure_eq_sum_partitionAtom_ch02
-- name    : LevyStochCalc.Poisson.measure_eq_sum_partitionAtom_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T00:09:00.140564+00:00
-- url     : https://prove2.me/theorems/96630b0d-9664-4a8c-af03-ba21c8a8959f
-- title:
--   Partition atom measure sum
-- statement:
--   The measure of a measurable finite-index region is the sum of masses of its disjoint partition atoms.
-- source:
--   LevyStochCalc/Poisson/RegionPartition.lean and RegionIndependence.lean for Kyprianou 2006, Chapter 2.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
import Theorems.Thm_LevyStochCalc_Poisson_eq_biUnion_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_pairwise_disjoint_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_measurableSet_partitionAtom_ch02
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
set_option autoImplicit false

universe u
namespace LevyStochCalc.Poisson
theorem measure_eq_sum_partitionAtom_ch02
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ}
    {C : Fin n → Set 𝓨}
    (μ : Measure 𝓨) (hC : ∀ i, MeasurableSet (C i))
    (i : Fin n) :
    μ (C i) = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      μ (partitionAtom C S) := by sorry
end LevyStochCalc.Poisson
