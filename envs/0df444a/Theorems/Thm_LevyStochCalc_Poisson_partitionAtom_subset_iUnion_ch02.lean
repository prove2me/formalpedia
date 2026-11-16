-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_partitionAtom_subset_iUnion_ch02
-- name    : LevyStochCalc.Poisson.partitionAtom_subset_iUnion_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:51:13.322565+00:00
-- url     : https://prove2.me/theorems/b5c0b334-7eb2-4d38-b37b-0b239e9f2287
-- title:
--   Chapter 2 partition atom: partitionAtom_subset_iUnion
-- statement:
--   Source-exact finite-set partition lemma needed to prove disjoint-region independence of Poisson random measure evaluations. The mathematical hypotheses are identical to the original source theorem.
-- source:
--   LevyStochCalc/Poisson/RegionPartition.lean, original partitionAtom_subset_iUnion, Apache-2.0

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
open MeasureTheory
set_option autoImplicit false

universe u
namespace LevyStochCalc.Poisson
variable {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨}
theorem partitionAtom_subset_iUnion_ch02 (S : Finset (Fin n)) :
    partitionAtom C S ⊆ ⋃ i, C i := by sorry
end LevyStochCalc.Poisson
