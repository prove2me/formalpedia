-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_idealFiniteAdeles
-- name    : GroundTheory.Global.mem_idealFiniteAdeles
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:26:32.655882+00:00
-- url     : https://prove2.me/theorems/1efc54ed-5485-4c82-95a4-6f8b3b181c84
-- title:
--   Global: mem ideal Finite Adeles
-- statement:
--   The Global construction uses the mem ideal Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L85-L88

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

theorem GroundTheory.Global.mem_idealFiniteAdeles {x : 𝔸ᶠ[K]} :
    x ∈ idealFiniteAdeles I ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (x v) ≤ exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by sorry
