-- Prove2me | Theorems.Thm_GlobalTheory_UnitPartition_contDiffAt_logMap
-- name    : GlobalTheory.UnitPartition.contDiffAt_logMap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:16.910687+00:00
-- url     : https://prove2.me/theorems/0be4e14c-58b6-4490-a9ad-5d089401ab24
-- title:
--   Unit Partition: cont Diff At log Map
-- statement:
--   The Unit Partition construction uses the cont Diff At log Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L55-L66

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

theorem GlobalTheory.UnitPartition.contDiffAt_logMap (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    ContDiffAt ℝ ∞ (logMap (K := K)) x := by sorry
