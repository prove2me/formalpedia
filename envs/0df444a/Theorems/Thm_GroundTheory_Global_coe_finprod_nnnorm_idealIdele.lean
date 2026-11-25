-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_finprod_nnnorm_idealIdele
-- name    : GroundTheory.Global.coe_finprod_nnnorm_idealIdele
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:09.818369+00:00
-- url     : https://prove2.me/theorems/35a56e94-8be3-5575-aac5-309c45334f43
-- title:
--   Global: coe finprod nnnorm ideal Idele
-- statement:
--   The Global construction uses the coe finprod nnnorm ideal Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L143-L148

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

theorem GroundTheory.Global.coe_finprod_nnnorm_idealIdele :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)⁻¹ := by sorry
