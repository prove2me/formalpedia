-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isLocallyConstant_of_add_valBall
-- name    : GroundTheory.LocalField.isLocallyConstant_of_add_valBall
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:19:11.974196+00:00
-- url     : https://prove2.me/theorems/ca30c37a-e779-4a71-a0bf-da2c59f52a95
-- title:
--   Local Field: is Locally Constant of add val Ball
-- statement:
--   The Local Field construction uses the is Locally Constant of add val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L27-L34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.isLocallyConstant_of_add_valBall {g : K → ℂ} {N : ℤ}
    (hg : ∀ x, ∀ h ∈ valBall K N, g (x + h) = g x) : IsLocallyConstant g := by sorry
