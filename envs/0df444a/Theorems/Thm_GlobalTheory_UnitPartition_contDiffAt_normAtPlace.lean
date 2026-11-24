-- Prove2me | Theorems.Thm_GlobalTheory_UnitPartition_contDiffAt_normAtPlace
-- name    : GlobalTheory.UnitPartition.contDiffAt_normAtPlace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:33.686802+00:00
-- url     : https://prove2.me/theorems/368625f5-6746-4867-8a56-e419b84ae07b
-- title:
--   Unit Partition: cont Diff At norm At Place
-- statement:
--   The Unit Partition construction uses the cont Diff At norm At Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L41-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L41-L53

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

theorem GlobalTheory.UnitPartition.contDiffAt_normAtPlace (w : InfinitePlace K) (x : mixedSpace K)
    (hx : normAtPlace w x ≠ 0) : ContDiffAt ℝ ∞ (fun y : mixedSpace K => normAtPlace w y) x := by sorry
