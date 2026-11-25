-- Prove2me | Theorems.Thm_GroundTheory_LocalField_multHaar_unitFiltrationUnits
-- name    : GroundTheory.LocalField.multHaar_unitFiltrationUnits
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:15.195501+00:00
-- url     : https://prove2.me/theorems/528f10d5-e17d-4bc8-b82b-926af57be50e
-- title:
--   Local Field: mult Haar unit Filtration Units
-- statement:
--   The Local Field construction uses the mult Haar unit Filtration Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L119-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L119-L141

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
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

theorem GroundTheory.LocalField.multHaar_unitFiltrationUnits {c : ℕ} (hc : 1 ≤ c) :
    (multHaar K (unitFiltrationUnits K c)).toReal =
      (multHaarConst K).toReal * (haarIntegers K).real (valBall K c) := by sorry
