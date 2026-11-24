-- Prove2me | Theorems.Thm_GlobalTheory_UnitLogPartition_continuous_proj
-- name    : GlobalTheory.UnitLogPartition.continuous_proj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:06.756925+00:00
-- url     : https://prove2.me/theorems/f38e741c-249e-4290-9089-d8b37582cf5c
-- title:
--   Unit Log Partition: continuous proj
-- statement:
--   The Unit Log Partition construction uses the continuous proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslate.lean#L100-L102

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

theorem GlobalTheory.UnitLogPartition.continuous_proj (hφ : GlobalTheory.CMVal.IsCMType φ) : Continuous (proj hφ) := by sorry
