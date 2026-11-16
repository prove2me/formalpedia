-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_eq_biUnion_partitionAtom_ch02
-- name    : LevyStochCalc.Poisson.eq_biUnion_partitionAtom_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:51:14.973708+00:00
-- url     : https://prove2.me/theorems/fa6964f3-6ddd-4abd-b603-e32935809c91
-- title:
--   Chapter 2 partition atom: eq_biUnion_partitionAtom
-- statement:
--   Source-exact finite-set partition lemma needed to prove disjoint-region independence of Poisson random measure evaluations. The mathematical hypotheses are identical to the original source theorem.
-- source:
--   LevyStochCalc/Poisson/RegionPartition.lean, original eq_biUnion_partitionAtom, Apache-2.0

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
open MeasureTheory
set_option autoImplicit false

universe u
namespace LevyStochCalc.Poisson
variable {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨}
theorem eq_biUnion_partitionAtom_ch02 (i : Fin n) :
    C i = ⋃ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), partitionAtom C S := by sorry
end LevyStochCalc.Poisson
