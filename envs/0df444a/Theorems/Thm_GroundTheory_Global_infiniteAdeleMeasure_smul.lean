-- Prove2me | Theorems.Thm_GroundTheory_Global_infiniteAdeleMeasure_smul
-- name    : GroundTheory.Global.infiniteAdeleMeasure_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:56.178203+00:00
-- url     : https://prove2.me/theorems/7fbcebef-d075-5a98-bb78-a1df295eb6b3
-- title:
--   Global: infinite Adele Measure smul
-- statement:
--   The Global construction uses the infinite Adele Measure smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleScaling.lean#L70-L82

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

theorem GroundTheory.Global.infiniteAdeleMeasure_smul (a : (InfiniteAdeleRing K)ˣ) (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K (a • E) =
      ENNReal.ofReal ‖(a : InfiniteAdeleRing K)‖ * infiniteAdeleMeasure K E := by sorry
