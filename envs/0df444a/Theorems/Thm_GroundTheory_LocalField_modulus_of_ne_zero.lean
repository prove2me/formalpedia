-- Prove2me | Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero
-- name    : GroundTheory.LocalField.modulus_of_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:12.743152+00:00
-- url     : https://prove2.me/theorems/12e8753b-2dec-4846-9ba6-7dd321607c4d
-- title:
--   Local Field: modulus of ne zero
-- statement:
--   The Local Field construction uses the modulus of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L127-L129

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.modulus_of_ne_zero {x : K} (hx : x ≠ 0) :
    modulus x = (residueCard K : ℝ≥0) ^ (-ord x) := by sorry
