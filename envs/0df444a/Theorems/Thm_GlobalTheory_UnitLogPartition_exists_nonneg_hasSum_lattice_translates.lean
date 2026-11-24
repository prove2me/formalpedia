-- Prove2me | Theorems.Thm_GlobalTheory_UnitLogPartition_exists_nonneg_hasSum_lattice_translates
-- name    : GlobalTheory.UnitLogPartition.exists_nonneg_hasSum_lattice_translates
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:59.92544+00:00
-- url     : https://prove2.me/theorems/9a44ff4a-6dec-403c-a684-406c358a3b73
-- title:
--   Unit Log Partition: exists nonneg has Sum lattice translates
-- statement:
--   The Unit Log Partition construction uses the exists nonneg has Sum lattice translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L16-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L16-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory
open GlobalTheory.UnitLogPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem GlobalTheory.UnitLogPartition.exists_nonneg_hasSum_lattice_translates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by sorry
