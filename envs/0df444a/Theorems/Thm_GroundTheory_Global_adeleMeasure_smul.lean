-- Prove2me | Theorems.Thm_GroundTheory_Global_adeleMeasure_smul
-- name    : GroundTheory.Global.adeleMeasure_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:56.080956+00:00
-- url     : https://prove2.me/theorems/9215d4c3-74b1-5203-b08a-5c0acb4487e7
-- title:
--   Global: adele Measure smul
-- statement:
--   The Global construction uses the adele Measure smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L152-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L152-L163

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

theorem GroundTheory.Global.adeleMeasure_smul (a : IdeleGroup K) (E : Set 𝔸[K]) :
    adeleMeasure K (a • E) = ENNReal.ofReal (IdeleGroup.ideleModule K a : ℝ) * adeleMeasure K E := by sorry
