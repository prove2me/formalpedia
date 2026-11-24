-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_bumpProd_sub
-- name    : GlobalTheory.LatticePartition.bumpProd_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:00:30.375471+00:00
-- url     : https://prove2.me/theorems/0ea77527-24e0-4218-b4f2-671ebb3f3690
-- title:
--   Lattice Partition: bump Prod sub
-- statement:
--   The Lattice Partition construction uses the bump Prod sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L89-L91

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

theorem GlobalTheory.LatticePartition.bumpProd_sub (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) (j : Fin n → ℤ) :
    bumpProd e (x - latPt e j) = ∏ i, bump (e x i - j i) := by sorry
