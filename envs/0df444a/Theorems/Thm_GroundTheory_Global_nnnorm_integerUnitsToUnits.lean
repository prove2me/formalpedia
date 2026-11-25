-- Prove2me | Theorems.Thm_GroundTheory_Global_nnnorm_integerUnitsToUnits
-- name    : GroundTheory.Global.nnnorm_integerUnitsToUnits
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:23.742422+00:00
-- url     : https://prove2.me/theorems/1bd604a5-aa64-4997-ab09-538db84526d1
-- title:
--   Global: nnnorm integer Units To Units
-- statement:
--   The Global construction uses the nnnorm integer Units To Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L282-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L282-L291

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

theorem GroundTheory.Global.nnnorm_integerUnitsToUnits (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((integerUnitsToUnits v u : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ = 1 := by sorry
