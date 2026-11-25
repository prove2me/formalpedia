-- Prove2me | Theorems.Thm_GroundTheory_Global_map_smul_adeleMeasure
-- name    : GroundTheory.Global.map_smul_adeleMeasure
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:26:46.926188+00:00
-- url     : https://prove2.me/theorems/c4d33633-ca26-4d2f-ae70-1e003b460fc9
-- title:
--   Global: map smul adele Measure
-- statement:
--   The Global construction uses the map smul adele Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L130-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L130-L150

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

theorem GroundTheory.Global.map_smul_adeleMeasure (a : IdeleGroup K) :
    (adeleMeasure K).map (fun x ↦ a • x) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ • adeleMeasure K := by sorry
