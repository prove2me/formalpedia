-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indicator_valBall_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.indicator_valBall_mem_schwartzBruhat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:05.669233+00:00
-- url     : https://prove2.me/theorems/6b3796c9-77c2-55dd-8f4f-bfb0b665fd57
-- title:
--   Local Field: indicator val Ball mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the indicator val Ball mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L82-L92

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

theorem GroundTheory.LocalField.indicator_valBall_mem_schwartzBruhat (k : ℤ) :
    (valBall K k : Set K).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat K := by sorry
