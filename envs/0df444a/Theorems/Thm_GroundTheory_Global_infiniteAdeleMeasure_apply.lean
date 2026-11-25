-- Prove2me | Theorems.Thm_GroundTheory_Global_infiniteAdeleMeasure_apply
-- name    : GroundTheory.Global.infiniteAdeleMeasure_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:50.776431+00:00
-- url     : https://prove2.me/theorems/6c0a6057-9ca8-5aa8-af4c-21a1ec3bb83d
-- title:
--   Global: infinite Adele Measure apply
-- statement:
--   The Global construction uses the infinite Adele Measure apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L65-L68

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
variable (K)

theorem GroundTheory.Global.infiniteAdeleMeasure_apply (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K E = selfDualMeasure K (homeomorphMixedSpace K '' E) := by sorry
