-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteIdeleMeasure_finiteIntegralUnits
-- name    : GroundTheory.Global.finiteIdeleMeasure_finiteIntegralUnits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:40:51.21022+00:00
-- url     : https://prove2.me/theorems/d03ddf1d-90ef-4708-ad24-82f4b2e39717
-- title:
--   Global: finite Idele Measure finite Integral Units
-- statement:
--   The Global construction uses the finite Idele Measure finite Integral Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L445-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L445-L447

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open InfinitePlace

theorem GroundTheory.Global.finiteIdeleMeasure_finiteIntegralUnits :
    finiteIdeleMeasure K (finiteIntegralUnits K) = 1 := by sorry
