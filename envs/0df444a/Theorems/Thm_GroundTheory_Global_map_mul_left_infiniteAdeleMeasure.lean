-- Prove2me | Theorems.Thm_GroundTheory_Global_map_mul_left_infiniteAdeleMeasure
-- name    : GroundTheory.Global.map_mul_left_infiniteAdeleMeasure
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:26:14.436813+00:00
-- url     : https://prove2.me/theorems/766ff5b2-d25f-4678-91c2-1489529e0d00
-- title:
--   Global: map mul left infinite Adele Measure
-- statement:
--   The Global construction uses the map mul left infinite Adele Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L84-L92

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

theorem GroundTheory.Global.map_mul_left_infiniteAdeleMeasure (b : (InfiniteAdeleRing K)ˣ) :
    (infiniteAdeleMeasure K).map (fun y ↦ (b : InfiniteAdeleRing K) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ •
        infiniteAdeleMeasure K := by sorry
