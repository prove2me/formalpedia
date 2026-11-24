-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_bump_local
-- name    : GlobalTheory.LatticePartition.bump_local
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:00:24.790618+00:00
-- url     : https://prove2.me/theorems/a16fc324-4579-46d3-8f11-8c626bc0bebf
-- title:
--   Lattice Partition: bump local
-- statement:
--   The Lattice Partition construction uses the bump local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L25-L36

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

theorem GlobalTheory.LatticePartition.bump_local (y : ℝ) (k : ℤ) (hk : k ∉ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ)) :
    bump (y - k) = 0 := by sorry
