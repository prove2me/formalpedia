-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_measurableSet_partitionAtom_ch02
-- name    : LevyStochCalc.Poisson.measurableSet_partitionAtom_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:51:11.635491+00:00
-- url     : https://prove2.me/theorems/c1fb9d1d-76a6-40ed-9b2e-5f66c3dade46
-- title:
--   Chapter 2 partition atom: measurableSet_partitionAtom
-- statement:
--   Source-exact finite-set partition lemma needed to prove disjoint-region independence of Poisson random measure evaluations. The mathematical hypotheses are identical to the original source theorem.
-- source:
--   LevyStochCalc/Poisson/RegionPartition.lean, original measurableSet_partitionAtom, Apache-2.0

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
open MeasureTheory
set_option autoImplicit false

universe u
namespace LevyStochCalc.Poisson
variable {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨}
theorem measurableSet_partitionAtom_ch02 (hC : ∀ i, MeasurableSet (C i)) (S : Finset (Fin n)) :
    MeasurableSet (partitionAtom C S) := by sorry
end LevyStochCalc.Poisson
