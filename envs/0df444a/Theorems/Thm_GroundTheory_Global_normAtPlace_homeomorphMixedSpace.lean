-- Prove2me | Theorems.Thm_GroundTheory_Global_normAtPlace_homeomorphMixedSpace
-- name    : GroundTheory.Global.normAtPlace_homeomorphMixedSpace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:29.526154+00:00
-- url     : https://prove2.me/theorems/c6e337f1-9dc0-5f14-b1be-007d8b9601c7
-- title:
--   Global: norm At Place homeomorph Mixed Space
-- statement:
--   The Global construction uses the norm At Place homeomorph Mixed Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L43-L51

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
omit [NumberField K]

theorem GroundTheory.Global.normAtPlace_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (homeomorphMixedSpace K x) = ‖x w‖ := by sorry
