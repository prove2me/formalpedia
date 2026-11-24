-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_bumpProd_compact
-- name    : GlobalTheory.LatticePartition.bumpProd_compact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:00:22.371269+00:00
-- url     : https://prove2.me/theorems/80ce38ed-3fbf-4662-bde9-7c248ede019c
-- title:
--   Lattice Partition: bump Prod compact
-- statement:
--   The Lattice Partition construction uses the bump Prod compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L76-L87

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

theorem GlobalTheory.LatticePartition.bumpProd_compact (e : V ≃L[ℝ] (Fin n → ℝ)) : HasCompactSupport (bumpProd e) := by sorry
