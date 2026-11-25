-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles_ne_top
-- name    : GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles_ne_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:31.534926+00:00
-- url     : https://prove2.me/theorems/c88eda8b-68eb-4cb0-9b19-a6c6c7debba5
-- title:
--   Global: finite Adele Measure integral Finite Adeles ne top
-- statement:
--   The Global construction uses the finite Adele Measure integral Finite Adeles ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L122-L125

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
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
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (K)

theorem GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles_ne_top :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ ∞ := by sorry
