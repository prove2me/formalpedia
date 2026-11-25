-- Prove2me | Theorems.Thm_GroundTheory_Global_map_normOneSplitting_eq_prod_at
-- name    : GroundTheory.Global.map_normOneSplitting_eq_prod_at
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:49.713668+00:00
-- url     : https://prove2.me/theorems/9ae6cc89-498c-427e-a5d7-2607ae4d2abb
-- title:
--   Global: map norm One Splitting eq prod at
-- statement:
--   The Global construction uses the map norm One Splitting eq prod at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L306-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L306-L308

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
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.map_normOneSplitting_eq_prod_at (w : InfinitePlace K) :
    (ideleMeasure K).map (normOneSplitting w) = (normOneMeasureAt w).prod posRealMeasure := by sorry
