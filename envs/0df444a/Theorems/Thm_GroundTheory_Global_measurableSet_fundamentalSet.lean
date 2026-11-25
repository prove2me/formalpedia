-- Prove2me | Theorems.Thm_GroundTheory_Global_measurableSet_fundamentalSet
-- name    : GroundTheory.Global.measurableSet_fundamentalSet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:19.205378+00:00
-- url     : https://prove2.me/theorems/ac07c8af-3f3b-4fef-8b3c-2e75a6f4c56d
-- title:
--   Global: measurable Set fundamental Set
-- statement:
--   The Global construction uses the measurable Set fundamental Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L101-L103

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
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
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.measurableSet_fundamentalSet : MeasurableSet (fundamentalSet K) := by sorry
