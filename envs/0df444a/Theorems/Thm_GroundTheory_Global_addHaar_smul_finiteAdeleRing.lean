-- Prove2me | Theorems.Thm_GroundTheory_Global_addHaar_smul_finiteAdeleRing
-- name    : GroundTheory.Global.addHaar_smul_finiteAdeleRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:19.852051+00:00
-- url     : https://prove2.me/theorems/cea3d23d-f991-4b88-b831-9a90bb34f6e1
-- title:
--   Global: add Haar smul finite Adele Ring
-- statement:
--   The Global construction uses the add Haar smul finite Adele Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L367-L370

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

theorem GroundTheory.Global.addHaar_smul_finiteAdeleRing (μ : Measure 𝔸ᶠ[K]) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : (𝔸ᶠ[K])ˣ) (E : Set 𝔸ᶠ[K]) :
    μ (u • E) = (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) * μ E := by sorry
