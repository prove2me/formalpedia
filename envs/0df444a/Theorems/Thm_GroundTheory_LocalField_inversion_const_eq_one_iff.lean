-- Prove2me | Theorems.Thm_GroundTheory_LocalField_inversion_const_eq_one_iff
-- name    : GroundTheory.LocalField.inversion_const_eq_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:30.552423+00:00
-- url     : https://prove2.me/theorems/3f626907-605c-483f-8287-7a9dd87c6fe5
-- title:
--   Local Field: inversion const eq one iff
-- statement:
--   The Local Field construction uses the inversion const eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L41-L59

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
omit [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.inversion_const_eq_one_iff (n : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    (residueCard K : ℝ) ^ (-n) * r ^ 2 = 1 ↔ r = (residueCard K : ℝ) ^ ((n : ℝ) / 2) := by sorry
