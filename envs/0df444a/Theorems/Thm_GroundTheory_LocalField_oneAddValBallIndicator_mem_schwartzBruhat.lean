-- Prove2me | Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.oneAddValBallIndicator_mem_schwartzBruhat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:13.125333+00:00
-- url     : https://prove2.me/theorems/51867c21-6ce1-5be6-8f77-01a2f6142ada
-- title:
--   Local Field: one Add Val Ball Indicator mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the one Add Val Ball Indicator mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L233-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L233-L247

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
variable [MeasurableSpace K] [BorelSpace K]
omit [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.oneAddValBallIndicator_mem_schwartzBruhat {c : ℤ} (hc : 0 ≤ c) :
    oneAddValBallIndicator c ∈ schwartzBruhat K := by sorry
