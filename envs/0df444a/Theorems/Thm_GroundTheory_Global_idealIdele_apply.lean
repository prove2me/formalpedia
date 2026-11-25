-- Prove2me | Theorems.Thm_GroundTheory_Global_idealIdele_apply
-- name    : GroundTheory.Global.idealIdele_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:26:49.788917+00:00
-- url     : https://prove2.me/theorems/1bc188c8-83b1-4efc-8c94-ba9f8dcfb2d9
-- title:
--   Global: ideal Idele apply
-- statement:
--   The Global construction uses the ideal Idele apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L109-L117

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
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem GroundTheory.Global.idealIdele_apply (x : HeightOneSpectrum (𝓞 K)) :
    ((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
      ((uniformizerUnit x ^ FractionalIdeal.count K x (I : FractionalIdeal (𝓞 K)⁰ K) :
        (x.adicCompletion K)ˣ) : x.adicCompletion K) := by sorry
