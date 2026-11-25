-- Prove2me | Theorems.Thm_GroundTheory_Global_isIntegralUnitAt_finiteSingleUnits_integerUnits
-- name    : GroundTheory.Global.isIntegralUnitAt_finiteSingleUnits_integerUnits
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:20:04.625867+00:00
-- url     : https://prove2.me/theorems/aaa60d4b-a60a-441a-96c9-5844e1c14ff7
-- title:
--   Global: is Integral Unit At finite Single Units integer Units
-- statement:
--   The Global construction uses the is Integral Unit At finite Single Units integer Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L270-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L270-L280

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
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
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.isIntegralUnitAt_finiteSingleUnits_integerUnits (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    IsIntegralUnitAt (finiteSingleUnits v (integerUnitsToUnits v u)) w := by sorry
