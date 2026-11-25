-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_uniformizerUnit_zpow
-- name    : GroundTheory.Global.norm_uniformizerUnit_zpow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:20.773593+00:00
-- url     : https://prove2.me/theorems/8d869106-7227-4c4d-8310-a5becbd79693
-- title:
--   Global: norm uniformizer Unit zpow
-- statement:
--   The Global construction uses the norm uniformizer Unit zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L37-L41

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

theorem GroundTheory.Global.norm_uniformizerUnit_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    ‖((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by sorry
