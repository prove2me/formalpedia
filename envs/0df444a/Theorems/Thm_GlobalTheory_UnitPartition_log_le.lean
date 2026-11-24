-- Prove2me | Theorems.Thm_GlobalTheory_UnitPartition_log_le
-- name    : GlobalTheory.UnitPartition.log_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:15.71072+00:00
-- url     : https://prove2.me/theorems/4b1a9e61-9424-42ca-8388-bdf930aceb47
-- title:
--   Unit Partition: log le
-- statement:
--   The Unit Partition construction uses the log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L74-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L74-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open GlobalTheory.UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.UnitPartition.log_le (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) :
    Real.log (normAtPlace w x) ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ +
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by sorry
