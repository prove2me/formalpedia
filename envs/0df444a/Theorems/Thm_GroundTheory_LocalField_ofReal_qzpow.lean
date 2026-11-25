-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ofReal_qzpow
-- name    : GroundTheory.LocalField.ofReal_qzpow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:25.549712+00:00
-- url     : https://prove2.me/theorems/bb9f71b7-21d6-5b29-82b3-6cb25ac2f316
-- title:
--   Local Field: of Real qzpow
-- statement:
--   The Local Field construction uses the of Real qzpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L38-L42

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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

theorem GroundTheory.LocalField.ofReal_qzpow (n : ℤ) :
    (((residueCard K : ℝ) ^ n : ℝ) : ℂ) = (residueCard K : ℂ) ^ (n : ℂ) := by sorry
