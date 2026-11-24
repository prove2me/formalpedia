-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_summable_lattice
-- name    : GlobalTheory.LatticePartition.summable_lattice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:21.05499+00:00
-- url     : https://prove2.me/theorems/0feee174-5b98-4260-bd69-7e2435e41b36
-- title:
--   Lattice Partition: summable lattice
-- statement:
--   The Lattice Partition construction uses the summable lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L52-L62

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

theorem GlobalTheory.LatticePartition.summable_lattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by sorry
