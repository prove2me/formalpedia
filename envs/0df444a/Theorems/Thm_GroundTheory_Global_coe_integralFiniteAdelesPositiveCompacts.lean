-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_integralFiniteAdelesPositiveCompacts
-- name    : GroundTheory.Global.coe_integralFiniteAdelesPositiveCompacts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:49.045555+00:00
-- url     : https://prove2.me/theorems/82046836-5292-47c1-8225-4d4964c6e991
-- title:
--   Global: coe integral Finite Adeles Positive Compacts
-- statement:
--   The Global construction uses the coe integral Finite Adeles Positive Compacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L41-L44

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

theorem GroundTheory.Global.coe_integralFiniteAdelesPositiveCompacts :
    (integralFiniteAdelesPositiveCompacts K : Set (FiniteAdeleRing (𝓞 K) K)) =
      integralFiniteAdeles (𝓞 K) K := by sorry
