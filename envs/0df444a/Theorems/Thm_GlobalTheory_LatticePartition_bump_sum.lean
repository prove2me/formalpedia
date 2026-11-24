-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_bump_sum
-- name    : GlobalTheory.LatticePartition.bump_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:00:34.549391+00:00
-- url     : https://prove2.me/theorems/5714891e-9323-4fae-82c8-cf93e5ec21b7
-- title:
--   Lattice Partition: bump sum
-- statement:
--   The Lattice Partition construction uses the bump sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L38-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition

theorem GlobalTheory.LatticePartition.bump_sum (y : ℝ) : ∑ k ∈ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ), bump (y - k) = 1 := by sorry
