-- Prove2me | Theorems.Thm_GroundTheory_Global_normOneMeasureAt_eq
-- name    : GroundTheory.Global.normOneMeasureAt_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:48.058973+00:00
-- url     : https://prove2.me/theorems/ac009917-9968-5686-975d-3d104bf2aff1
-- title:
--   Global: norm One Measure At eq
-- statement:
--   The Global construction uses the norm One Measure At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L323-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L323-L352

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.normOneMeasureAt_eq (w w' : InfinitePlace K) :
    normOneMeasureAt w' = normOneMeasureAt w := by sorry
