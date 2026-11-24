-- Prove2me | Theorems.Thm_GlobalTheory_UnitLogPartition_idx_surjective
-- name    : GlobalTheory.UnitLogPartition.idx_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:53.044777+00:00
-- url     : https://prove2.me/theorems/0021e43a-647c-4598-8225-d398e2ee03ad
-- title:
--   Unit Log Partition: idx surjective
-- statement:
--   The Unit Log Partition construction uses the idx surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L71-L73

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
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}

theorem GlobalTheory.UnitLogPartition.idx_surjective (hφ : GlobalTheory.CMVal.IsCMType φ) (i : I) : ∃ w, idx hφ w = i := by sorry
