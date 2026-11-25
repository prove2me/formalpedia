-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_idealFiniteAdeles
-- name    : GroundTheory.Global.finiteAdeleMeasure_idealFiniteAdeles
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:02.000232+00:00
-- url     : https://prove2.me/theorems/db4d3209-15fe-52b7-ab6f-de4dd5149560
-- title:
--   Global: finite Adele Measure ideal Finite Adeles
-- statement:
--   The Global construction uses the finite Adele Measure ideal Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L150-L155

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

theorem GroundTheory.Global.finiteAdeleMeasure_idealFiniteAdeles :
    finiteAdeleMeasure K (idealFiniteAdeles I) =
      ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ))⁻¹ *
        ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by sorry
