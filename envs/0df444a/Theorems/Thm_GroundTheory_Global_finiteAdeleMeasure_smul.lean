-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_smul
-- name    : GroundTheory.Global.finiteAdeleMeasure_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:42.32556+00:00
-- url     : https://prove2.me/theorems/a1f4f92c-21fd-4c56-88e0-fed0523aef1c
-- title:
--   Global: finite Adele Measure smul
-- statement:
--   The Global construction uses the finite Adele Measure smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L372-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L372-L375

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

theorem GroundTheory.Global.finiteAdeleMeasure_smul (u : (𝔸ᶠ[K])ˣ) (E : Set 𝔸ᶠ[K]) :
    finiteAdeleMeasure K (u • E) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) * finiteAdeleMeasure K E := by sorry
