-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_units_smul_integralFiniteAdeles_iff
-- name    : GroundTheory.Global.mem_units_smul_integralFiniteAdeles_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:23.235478+00:00
-- url     : https://prove2.me/theorems/34e35887-8e34-597a-8f46-14c504f1fccd
-- title:
--   Global: mem units smul integral Finite Adeles iff
-- statement:
--   The Global construction uses the mem units smul integral Finite Adeles iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L60-L67

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

theorem GroundTheory.Global.mem_units_smul_integralFiniteAdeles_iff (u : (𝔸ᶠ[K])ˣ) (y : 𝔸ᶠ[K]) :
    y ∈ u • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ((u : 𝔸ᶠ[K]) v)⁻¹ * y v ∈ v.adicCompletionIntegers K := by sorry
