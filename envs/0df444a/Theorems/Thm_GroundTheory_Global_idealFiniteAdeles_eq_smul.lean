-- Prove2me | Theorems.Thm_GroundTheory_Global_idealFiniteAdeles_eq_smul
-- name    : GroundTheory.Global.idealFiniteAdeles_eq_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:21.263825+00:00
-- url     : https://prove2.me/theorems/04d4f805-50c3-4dba-87b6-9ccfb3eaaaf2
-- title:
--   Global: ideal Finite Adeles eq smul
-- statement:
--   The Global construction uses the ideal Finite Adeles eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L119-L125

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

theorem GroundTheory.Global.idealFiniteAdeles_eq_smul :
    (idealFiniteAdeles I : Set 𝔸ᶠ[K]) =
      idealIdele I • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) := by sorry
