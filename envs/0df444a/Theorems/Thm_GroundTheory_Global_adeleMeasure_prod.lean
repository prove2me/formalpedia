-- Prove2me | Theorems.Thm_GroundTheory_Global_adeleMeasure_prod
-- name    : GroundTheory.Global.adeleMeasure_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:04.643561+00:00
-- url     : https://prove2.me/theorems/26eca137-f7df-485f-b67b-d071730e3c6a
-- title:
--   Global: adele Measure prod
-- statement:
--   The Global construction uses the adele Measure prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L97-L99

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

theorem GroundTheory.Global.adeleMeasure_prod (A : Set (InfiniteAdeleRing K)) (B : Set (FiniteAdeleRing (𝓞 K) K)) :
    adeleMeasure K (A ×ˢ B) = infiniteAdeleMeasure K A * finiteAdeleMeasure K B := by sorry
