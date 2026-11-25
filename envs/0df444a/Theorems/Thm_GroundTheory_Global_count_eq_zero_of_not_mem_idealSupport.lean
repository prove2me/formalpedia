-- Prove2me | Theorems.Thm_GroundTheory_Global_count_eq_zero_of_not_mem_idealSupport
-- name    : GroundTheory.Global.count_eq_zero_of_not_mem_idealSupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:17.483953+00:00
-- url     : https://prove2.me/theorems/d03d42b8-fafc-470f-9dae-2b1d56de1c3b
-- title:
--   Global: count eq zero of not mem ideal Support
-- statement:
--   The Global construction uses the count eq zero of not mem ideal Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L101-L103

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

theorem GroundTheory.Global.count_eq_zero_of_not_mem_idealSupport {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ idealSupport I) : FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by sorry
