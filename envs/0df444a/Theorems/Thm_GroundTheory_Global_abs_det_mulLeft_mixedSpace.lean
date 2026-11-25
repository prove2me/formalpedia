-- Prove2me | Theorems.Thm_GroundTheory_Global_abs_det_mulLeft_mixedSpace
-- name    : GroundTheory.Global.abs_det_mulLeft_mixedSpace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:07.578177+00:00
-- url     : https://prove2.me/theorems/6f28d3bc-2301-5ca5-9553-f60e3151e0ff
-- title:
--   Global: abs det mul Left mixed Space
-- statement:
--   The Global construction uses the abs det mul Left mixed Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L30-L39

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.abs_det_mulLeft_mixedSpace (c : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ c)| = mixedEmbedding.norm c := by sorry
