-- Prove2me | Theorems.Thm_GlobalTheory_LatticePartition_summable_latPt
-- name    : GlobalTheory.LatticePartition.summable_latPt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:19.652806+00:00
-- url     : https://prove2.me/theorems/4b71843c-bdfd-4081-bad5-837f9d909a73
-- title:
--   Lattice Partition: summable lat Pt
-- statement:
--   The Lattice Partition construction uses the summable lat Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnity.lean#L111-L128

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

theorem GlobalTheory.LatticePartition.summable_latPt [FiniteDimensional ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ∃ M : ℕ, Summable (fun j : Fin n → ℤ => ((1 + ‖latPt b.equivFunL j‖) ^ M)⁻¹) := by sorry
