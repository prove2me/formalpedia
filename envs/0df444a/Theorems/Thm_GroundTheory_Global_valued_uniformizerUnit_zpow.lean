-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_uniformizerUnit_zpow
-- name    : GroundTheory.Global.valued_uniformizerUnit_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:23.694956+00:00
-- url     : https://prove2.me/theorems/800971b7-0ebf-48c6-ba8b-01491981609c
-- title:
--   Global: valued uniformizer Unit zpow
-- statement:
--   The Global construction uses the valued uniformizer Unit zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L30-L35

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.valued_uniformizerUnit_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Valued.v (((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      exp (-n) := by sorry
