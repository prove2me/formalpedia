-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_pairwise_disjoint_partitionAtom_ch02
-- name    : LevyStochCalc.Poisson.pairwise_disjoint_partitionAtom_ch02
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:51:08.3762+00:00
-- url     : https://prove2.me/theorems/e1e05e5f-0e9c-46b8-a7a5-e85a6a68b402
-- title:
--   Chapter 2 partition atom: pairwise_disjoint_partitionAtom
-- statement:
--   Source-exact finite-set partition lemma needed to prove disjoint-region independence of Poisson random measure evaluations. The mathematical hypotheses are identical to the original source theorem.
-- source:
--   LevyStochCalc/Poisson/RegionPartition.lean, original pairwise_disjoint_partitionAtom, Apache-2.0

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
open MeasureTheory
set_option autoImplicit false

universe u
namespace LevyStochCalc.Poisson
variable {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ} {C : Fin n → Set 𝓨}
theorem pairwise_disjoint_partitionAtom_ch02 :
    Pairwise fun S T => Disjoint (partitionAtom C S) (partitionAtom C T) := by sorry
end LevyStochCalc.Poisson
